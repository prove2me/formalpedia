-- Prove2me | Theorems.Thm_TruncLowDeg_Recovery_lemma_5_4
-- name    : TruncLowDeg.Recovery.lemma_5_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T05:25:32.594871+00:00
-- url     : https://prove2.me/theorems/ff67eaa8-46e4-443a-9cc8-da6993900b77
-- title:
--   Lemma 5.4 — preconditioning by the empirical mean and covariance of a preliminary batch ([LMZ24])
-- statement:
--   Let $\mu_0\in\mathbb R^d$, $\Sigma_0\succ0$, $\alpha_0,\delta>0$ and $S_0\subseteq\mathbb R^d$ with $\mathcal N(\mu_0,\Sigma_0)(S_0)\ge\alpha_0$, and let $X\sim\mathcal N(\mu_0,\Sigma_0)|_{S_0}$. From an independent preliminary batch of $n_{pre}=\tilde O(d^3\alpha_0^{-10}\log^2(1/\delta))$ samples compute the empirical mean and covariance $(\hat\mu_{pre},\hat\Sigma_{pre})$ and set $T(x)=\hat\Sigma_{pre}^{-1/2}(x-\hat\mu_{pre})$. Conditional on the batch, $T(X)\sim\mathcal N(\mu,\Sigma)|_S$ for
--   $$\mu=\hat\Sigma_{pre}^{-1/2}(\mu_0-\hat\mu_{pre}),\qquad \Sigma=\hat\Sigma_{pre}^{-1/2}\Sigma_0\hat\Sigma_{pre}^{-1/2},\qquad S=T(S_0).$$
--   With probability at least $1-\delta$, $\|\Sigma^{-1/2}\mu\|_2\le O(\sqrt{\log(1/\alpha_0)})$ and $\Omega(\alpha_0^2)I\preceq\Sigma\preceq O(1/\alpha_0^2)I$. Moreover $\mathcal N(\mu,\Sigma)(S)=\mathcal N(\mu_0,\Sigma_0)(S_0)$ and $\mathrm{BVD}(S)=\mathrm{BVD}(S_0)$.
--
--   Formally: one constant $C>0$ such that for every batch size $m\ge C d^3\alpha_0^{-10}(1+\log(d/\alpha_0))^C\log^2(1/\delta)$, (i) for every batch $b$ with $\hat\Sigma_{pre}\succ0$ the law of $T_b(X)$ is $\mathcal N(\mu,\Sigma)|_{T_b(S_0)}$, the mass and the BVD are preserved, and (ii) the batch fails "$\hat\Sigma_{pre}\succ0$, $\|\Sigma^{-1/2}\mu\|_2\le C\sqrt{\log(1/\alpha_0)}$, $(\alpha_0^2/C)I\preceq\Sigma\preceq(C/\alpha_0^2)I$" with probability at most $\delta$. The lemma puts the unknown Gaussian into a near-isotropic position, which fixes the scale $\rho$ of the cube used by Algorithm 1. It is cited from [LMZ24] and is false as printed at $\alpha_0=1$ and for $\delta$ close to $1$ (findings I2, I3).
--
--   Differences from the source:
--
--   - encoding: each O(·), Ω(·), Õ(·) → one explicit constant C, existentially quantified before every other variable it is uniform over; reason: the single-constant form is equivalent to separate constants (take the maximum)
--   - reading: n_pre = Õ(d³/α₀¹⁰ · log²(1/δ)) → every batch size m ≥ C · d³/α₀¹⁰ · (1 + log(d/α₀))^C · log²(1/δ); reason: Õ hides a factor polylogarithmic in d/α₀; requiring the claim for every m above the threshold is the stronger reading (more samples do not hurt)
--   - encoding: conditional on the preliminary batch, T(X) ∼ N(µ, Σ)|S → for every batch b with Σ̂_pre ≻ 0, the pushforward of N(µ₀, Σ₀)|S₀ under T_b equals N(µ, Σ)|T_b(S₀); reason: X is independent of the batch, so its conditional law given b is the law of T_b(X)
--   - encoding: the invertible affine transformation T → the deterministic clauses assume Σ̂_pre ≻ 0, and the probability clause counts a singular Σ̂_pre as a failure; reason: T is defined and invertible exactly when Σ̂_pre ≻ 0; nondegeneracy only
--   - encoding: Σ = Σ̂_pre^{−1/2} Σ₀ Σ̂_pre^{−1/2} → `SigT Σ₀ W = W Σ₀ Wᵀ` with W = Σ̂_pre^{−1/2} = (CFC.sqrt Σ̂_pre)⁻¹; reason: W is symmetric, so the two are equal
--   - reading: empirical / sample covariance → normalization 1/m (`empCov`); reason: the paper does not fix the normalization; Lemma 5.4 holds for either
--   - encoding: with probability at least 1 − δ → the product measure of the failure set is at most δ; reason: a lower bound on a possibly non-measurable success set would be read as an outer measure, which is weaker
--   - encoding: ℝ^d, coordinates j ∈ {1, …, d} → `Vec d = EuclideanSpace ℝ (Fin d)`, 0-based coordinates `Fin d`; reason: Lean convention; same instances
-- source:
--   Vári-Kakas, Wiedmer, A General Approach to Polynomial-Time Truncated Learning via Low-Degree Moments, STOC 2027 submission (manuscript sha256 613f0e39…), p. 21, Lemma 5.4 ([LMZ24, Theorem A.4 and Section 9.1]); proof p. 22

import Definitions.Def_TruncLowDeg_Recovery_Algorithm

open MeasureTheory ProbabilityTheory
open scoped MatrixOrder

namespace TruncLowDeg.Recovery

/-- Lemma 5.4 (p. 21, [LMZ24, Theorem A.4 and Section 9.1]): preconditioning with the empirical
mean and covariance of an independent preliminary batch. One universal constant `C` stands for
every `O(·)`, `Ω(·)` and `Õ(·)`; the batch size `n_pre = Õ(d³/α₀¹⁰ · log²(1/δ))` is read as any
`m ≥ C · d³/α₀¹⁰ · (1 + log(d/α₀))^C · log²(1/δ)`. For every batch `b` whose empirical
covariance `Σ̂_pre` is positive definite, with `T(x) = Σ̂_pre^{−1/2}(x − µ̂_pre)`,
`µ = Σ̂_pre^{−1/2}(µ₀ − µ̂_pre)` and `Σ = Σ̂_pre^{−1/2} Σ₀ Σ̂_pre^{−1/2}` (written `W Σ₀ Wᵀ` with
the symmetric `W = Σ̂_pre^{−1/2}`): the law of `T(X)` for an independent `X ∼ N(µ₀, Σ₀)|S₀` is
`N(µ, Σ)|T(S₀)`, `N(µ, Σ)(T(S₀)) = N(µ₀, Σ₀)(S₀)` and `BVD(T(S₀)) = BVD(S₀)`. The batch has
probability at most `δ` of failing `Σ̂_pre ≻ 0`, `‖Σ^{−1/2}µ‖₂ ≤ C √log(1/α₀)` and
`(α₀²/C) I ⪯ Σ ⪯ (C/α₀²) I`. -/
theorem lemma_5_4 :
    ∃ C : ℝ, 0 < C ∧
      ∀ (d : ℕ) (μ₀ : Vec d) (Sig₀ : Mat d), Sig₀.PosDef →
      ∀ (α₀ δ : ℝ), 0 < α₀ → 0 < δ →
      ∀ S₀ : Set (Vec d), ENNReal.ofReal α₀ ≤ gaussian μ₀ Sig₀ S₀ →
      ∀ m : ℕ, C * (d : ℝ) ^ 3 / α₀ ^ 10 * (1 + Real.log ((d : ℝ) / α₀)) ^ C *
          Real.log (1 / δ) ^ 2 ≤ m →
        (∀ b : Fin m → Vec d, (empCov (List.ofFn b)).PosDef →
          (truncGaussian μ₀ Sig₀ S₀).map
              (Tmap (empMean (List.ofFn b)) (invSqrt (empCov (List.ofFn b)))) =
            truncGaussian (muT μ₀ (empMean (List.ofFn b)) (invSqrt (empCov (List.ofFn b))))
              (SigT Sig₀ (invSqrt (empCov (List.ofFn b))))
              (Tmap (empMean (List.ofFn b)) (invSqrt (empCov (List.ofFn b))) '' S₀) ∧
          gaussian (muT μ₀ (empMean (List.ofFn b)) (invSqrt (empCov (List.ofFn b))))
              (SigT Sig₀ (invSqrt (empCov (List.ofFn b))))
              (Tmap (empMean (List.ofFn b)) (invSqrt (empCov (List.ofFn b))) '' S₀) =
            gaussian μ₀ Sig₀ S₀ ∧
          BVD (Tmap (empMean (List.ofFn b)) (invSqrt (empCov (List.ofFn b))) '' S₀) =
            BVD S₀) ∧
        (Measure.pi fun _ : Fin m => truncGaussian μ₀ Sig₀ S₀)
          {b | ¬ ((empCov (List.ofFn b)).PosDef ∧
            PrecondOK C α₀ (muT μ₀ (empMean (List.ofFn b)) (invSqrt (empCov (List.ofFn b))))
              (SigT Sig₀ (invSqrt (empCov (List.ofFn b)))))} ≤ ENNReal.ofReal δ := by sorry

end TruncLowDeg.Recovery
