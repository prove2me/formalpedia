-- Prove2me | Theorems.Thm_TruncLowDeg_Recovery_lemma_6_2
-- name    : TruncLowDeg.Recovery.lemma_6_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T05:25:27.958826+00:00
-- url     : https://prove2.me/theorems/6c5178c0-b8ab-4a0e-8404-03909b54d085
-- title:
--   Lemma 6.2 — preconditioning and clipping: Lemma 5.4's bounds, mass $\ge\alpha_0/2$, $\mathrm{BVD}(S)\le3k$, and i.i.d. retained samples
-- statement:
--   In the setting of Theorem 6.1 let $\mu=\hat\Sigma_{pre}^{-1/2}(\mu_0-\hat\mu_{pre})$, $\Sigma=\hat\Sigma_{pre}^{-1/2}\Sigma_0\hat\Sigma_{pre}^{-1/2}$ and $S=T(S_0)\cap\{x:\|x\|_2\le\rho\}$. With probability at least $1-\delta/2$, $\mu$ and $\Sigma$ satisfy the conclusions of Lemma 5.4,
--   $$\mathcal N(\mu,\Sigma)(S)\ge\alpha_0/2\qquad\text{and}\qquad \mathrm{BVD}(S)\le3k .$$
--   On this event, conditional on the preliminary batch and the number of retained samples, the points of $\hat{\mathcal D}$ are independent samples from $\mathcal N(\mu,\Sigma)|_S$.
--
--   Formally: there are a constant $C_4$ (for Lemma 5.4's $O(\cdot)$, $\Omega(\cdot)$) and a threshold $N$ such that for batch and $\rho$-constants at least $N$: (i) the batch $b$ of $n_{pre}$ i.i.d. samples from $\mathcal N(\mu_0,\Sigma_0)|_{S_0}$ fails "$\hat\Sigma_{pre}\succ0$ and, for every whitening $W$ of $\hat\Sigma_{pre}$, the preconditioning succeeds for $W(\mu_0-\hat\mu_{pre})$, $W\Sigma_0W^\top$, $T(S_0)\cap\{\|x\|_2\le\rho\}$" with probability at most $\delta/2$; (ii) for such a batch, a whitening $W$, any number $n_{rec}$ of i.i.d. recovery samples $Y$, every $m$ and every measurable $A\subseteq(\mathbb R^d)^m$,
--   $$\mathbb P_Y\big[\hat{\mathcal D}=(z_1,\dots,z_m)\text{ with }z\in A\big]=\mathbb P_Y\big[|\hat{\mathcal D}|=m\big]\cdot\big(\mathcal N(\mu,\Sigma)|_S\big)^{\otimes m}(A).$$
--   This is the probabilistic input to Proposition 6.7: it reduces the analysis to i.i.d. samples of a near-isotropic truncated Gaussian on a bounded set of boundary vanishing degree at most $3k$.
--
--   Differences from the source:
--
--   - encoding: the constants of Lemma 5.4 and "ρ = O(√d/α₀²) with a sufficiently large implicit constant", the batch size → ∃ C₄ > 0 and ∃ N such that the claim holds for every algorithm constant vector c with c_pre ≥ N and c_ρ ≥ N; reason: the paper's implicit constants, made explicit in the order they are chosen
--   - reading: a preliminary batch "of the size required by Lemma 5.4 with failure probability δ/2" (Õ(d³/α₀¹⁰ · log²(2/δ))) → `nPre = ⌈c_pre · d⁴/(α₀¹¹ δ)⌉` with the batch constant c_pre sufficiently large; reason: it dominates Lemma 5.4's requirement for large c_pre (polylog(d/α₀) ≤ O(d/α₀), log²(2/δ) = O(1/δ), as the paper notes on p. 28), is absorbed in the sample bound, and is computable with field operations and comparisons only (Lemma 6.8)
--   - generalization: line 4's T(x) = Σ̂_pre^{−1/2}(x − µ̂_pre) and line 14's Σ̂_pre^{1/2} → any whitening W of Σ̂_pre (W Σ̂_pre Wᵀ = I) in line 4 and W⁻¹ in line 14; the statement holds for every such W; reason: Σ̂_pre^{−1/2} is a whitening (then W⁻¹ = Σ̂_pre^{1/2}), so it specializes to the paper's algorithm; every whitening is QΣ̂_pre^{−1/2} with Q orthogonal, and the variant is what an exact implementation can compute (Lemma 6.8)
--   - encoding: conditional on the preliminary batch and the number of retained samples, the points in 𝒟̂ are independent samples from N(µ, Σ)|S → for every good batch b and whitening W, every n_rec, m and measurable A ⊆ (ℝ^d)^m: P_Y[𝒟̂ = List.ofFn z with z ∈ A] = P_Y[|𝒟̂| = m] · (N(µ, Σ)|S)^{⊗m}(A), Y the n_rec i.i.d. recovery samples; reason: this identity is the definition of the conditional law given the retained count; the batch is fixed because it is independent of Y
--   - generalization: the setting of Theorem 6.1 (n ≥ (1/(δε²))(d/α₀)^{O(k)} samples, ε ∈ (0, 1)) → the batch of n_pre samples and any number n_rec of recovery samples; n and ε do not appear; reason: neither clause depends on n or ε; n_rec = n − n_pre specializes it
--   - reading: empirical / sample covariance → normalization 1/m (`empCov`); reason: the paper does not fix the normalization; Lemma 5.4 holds for either
--   - encoding: with probability at least 1 − δ → the product measure of the failure set is at most δ; reason: a lower bound on a possibly non-measurable success set would be read as an outer measure, which is weaker
--   - encoding: ℝ^d, coordinates j ∈ {1, …, d} → `Vec d = EuclideanSpace ℝ (Fin d)`, 0-based coordinates `Fin d`; reason: Lean convention; same instances
-- source:
--   Vári-Kakas, Wiedmer, A General Approach to Polynomial-Time Truncated Learning via Low-Degree Moments, STOC 2027 submission (manuscript sha256 613f0e39…), p. 27, Lemma 6.2; proof p. 27

import Definitions.Def_TruncLowDeg_Recovery_Algorithm

open MeasureTheory ProbabilityTheory
open scoped MatrixOrder

namespace TruncLowDeg.Recovery

/-- Lemma 6.2 (p. 27): preconditioning and clipping. There are a constant `C₄` (for Lemma 5.4's
`O(·)`, `Ω(·)`) and a threshold `N` such that, for Algorithm 1 with batch constant and
`ρ`-constant at least `N`, in the setting of Theorem 6.1:
(i) over the preliminary batch `b` (`nPre` i.i.d. samples from `N(µ₀, Σ₀)|S₀`), the event
"`Σ̂_pre ≻ 0` and, for the whitening `W` used in line 4, `µ = W(µ₀ − µ̂_pre)`, `Σ = W Σ₀ Wᵀ`
satisfy the conclusions of Lemma 5.4, `N(µ, Σ)(S) ≥ α₀/2` and `BVD(S) ≤ 3k` for
`S = T(S₀) ∩ {‖x‖₂ ≤ ρ}`" fails with probability at most `δ/2`;
(ii) on this event, conditional on the batch and on the number `m` of retained samples, the
points of `𝒟̂` are `m` independent samples from `N(µ, Σ)|S`: for i.i.d. recovery samples `Y`,
`P[𝒟̂ = (z₁, …, z_m) with z ∈ A] = P[|𝒟̂| = m] · (N(µ,Σ)|S)^{⊗m}(A)` for every measurable `A`.
The paper's whitening is `W = Σ̂_pre^{−1/2}`; the statement holds for every whitening. -/
theorem lemma_6_2 :
    ∃ C₄ : ℝ, 0 < C₄ ∧ ∃ N : ℕ, ∀ c : Consts, N ≤ c.pre → N ≤ c.rho →
      ∀ (d k : ℕ) (α₀ δ : ℝ) (μ₀ : Vec d) (Sig₀ : Mat d) (S₀ : Set (Vec d)),
      1 ≤ d → 1 ≤ k → 0 < α₀ → α₀ ≤ 1 → Sig₀.PosDef → BVD S₀ ≤ (k : ℕ∞) →
      ENNReal.ofReal α₀ ≤ gaussian μ₀ Sig₀ S₀ → 0 < δ → δ < 1 →
        (Measure.pi fun _ : Fin (nPre c d α₀ δ) => truncGaussian μ₀ Sig₀ S₀)
            {b | ¬ ((empCov (List.ofFn b)).PosDef ∧
              ∀ W : Mat d, IsWhitening (empCov (List.ofFn b)) W →
                Success C₄ k α₀ (muT μ₀ (empMean (List.ofFn b)) W) (SigT Sig₀ W)
                  (ST S₀ (empMean (List.ofFn b)) W (rhoV c d α₀)))} ≤
          ENNReal.ofReal (δ / 2) ∧
        ∀ (b : Fin (nPre c d α₀ δ) → Vec d) (W : Mat d),
          (empCov (List.ofFn b)).PosDef → IsWhitening (empCov (List.ofFn b)) W →
          Success C₄ k α₀ (muT μ₀ (empMean (List.ofFn b)) W) (SigT Sig₀ W)
            (ST S₀ (empMean (List.ofFn b)) W (rhoV c d α₀)) →
          ∀ (nrec m : ℕ) (A : Set (Fin m → Vec d)), MeasurableSet A →
            (Measure.pi fun _ : Fin nrec => truncGaussian μ₀ Sig₀ S₀)
                {Y | ∃ z ∈ A, Dhat c α₀ δ (List.ofFn b ++ List.ofFn Y) W = List.ofFn z} =
              (Measure.pi fun _ : Fin nrec => truncGaussian μ₀ Sig₀ S₀)
                  {Y | (Dhat c α₀ δ (List.ofFn b ++ List.ofFn Y) W).length = m} *
                (Measure.pi fun _ : Fin m =>
                  truncGaussian (muT μ₀ (empMean (List.ofFn b)) W) (SigT Sig₀ W)
                    (ST S₀ (empMean (List.ofFn b)) W (rhoV c d α₀))) A := by sorry

end TruncLowDeg.Recovery
