-- Prove2me | Theorems.Thm_SelfSelReg_Supplement_theorem_8_1
-- name    : SelfSelReg.Supplement.theorem_8_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-22T05:21:44.119589+00:00
-- url     : https://prove2.me/theorems/d29d8c30-d973-4a5f-8e9e-b579b380192e
-- title:
--   Theorem 8.1 — Hermite moment estimation by peeling
-- statement:
--   Consider the Gaussian self-selection model with regressors $w_1,\dots,w_k\in\mathbb R^n$, $2\le k\le n$, under Assumption 1.2 with constants $B\ge1$, $\Delta\in(0,1]$, and the hyperparameters $K$, $T$, $s$ of the paper. Let $2\le r\le s$ and fix a projection map $U\in\mathbb R^{p\times n^r}$ with orthonormal rows. Assume fresh samples $(X,U\widetilde X^{\otimes r},Y_{\max})$ are given, where $\widetilde X=X+\mathrm iX'$ and $X'\sim N(0,I_n)$ is independent of the observation. Fix a sampling accuracy $\varepsilon_{\mathrm{est}}\in(0,1)$ and a failure probability $\delta\in(0,1/3)$. Let $\widehat{\mathcal R}$ be a list of regressor estimates matched to some $R\subsetneq[k]$ with $\|\widehat w-w_{\mathrm{match}(\widehat w)}\|_2\le e^{-K^6s}$ for every $\widehat w\in\widehat{\mathcal R}$, and put $Q=[k]\setminus R$. Write $T^Q_d$ for the restricted Hermite moment of order $d$ and $A_Q^{(r)}$ for the even target of (38).
--
--   1. For the projected even moment at order $r$, ESTIMATEMOMENTSBYPEELING (Algorithm 8.1) returns a symmetric matrix $\widehat M\in\mathbb R^{p\times p}$ satisfying, with probability at least $1-\delta$,
--   $$
--   \bigl\|\widehat M-U\operatorname{Mat}_r(T^Q_{2r})U^\top\bigr\|_F\le\varepsilon_{\mathrm{est}}+\frac{\sqrt k}{\sqrt{2\pi}}e^{-K^6s}+e^{4s\log K-T^2/(2K)}\,k\operatorname{tr}(A_Q^{(r)}).
--   $$
--   2. For the projected odd moment at $r=s$, it returns symmetric matrices $\widehat M_1,\dots,\widehat M_n\in\mathbb R^{p\times p}$ satisfying, with probability at least $1-\delta$, simultaneously for every $b\in\mathbb R^n$,
--   $$
--   \Bigl\|\sum_{\ell=1}^nb_\ell\widehat M_\ell-U\operatorname{Mat}_s(T^Q_{2s+1}\,\lrcorner\,b)U^\top\Bigr\|_F\le\Bigl(\varepsilon_{\mathrm{est}}+\frac{\sqrt k}{\sqrt{2\pi}}e^{-K^6s}+e^{4s\log K-T^2/(2K)}\,k\operatorname{tr}(A_Q^{(s)})\Bigr)\|b\|_2 .
--   $$
--
--   Each call requires at most $\widetilde O\bigl((p^2n/\varepsilon_{\mathrm{est}}^2)\,100^s\log(1/\delta)\bigr)$ projected samples, and its running time is at most $\mathrm{poly}(n,k,p,1/\varepsilon_{\mathrm{est}},\log(1/\delta))$.
--
--   This is the moment-estimation oracle of the paper: it estimates moments restricted to the unrecovered regressors although only the overall maximum $Y_{\max}$ is observed, with an explicit sampling error, an error from the inaccuracy of the recovered list, and a bias from the peeling weight.
--
--   **Formalization Note** The routine is one program of the sampling real RAM of the base mission, restricted to exact arithmetic, comparisons, fair coins and sample reads, fixed with one constant $C$ before all parameters; a mode in its input selects the even or the odd call. The map $U$ is not an input. For the odd call a sample also carries $X'$. The sample bound is $C(p^2n/\varepsilon_{\mathrm{est}}^2)\,100^s(1+\log(np/\varepsilon_{\mathrm{est}}))^C\log(1/\delta)$ and the work bound is $C\,(n+k+p+1/\varepsilon_{\mathrm{est}}+\log(1/\delta))^{CK^C}$, on every run. The returned matrices are symmetric on every run, and in part 2 one event of probability at least $1-\delta$ serves all $b$.
--
--   Differences from the source:
--
--   - reading: "ESTIMATEMOMENTSBYPEELING (Algorithm 8.1) returns …", "its sample complexity is …", "its running time is …", with no machine named; the pseudocode uses exact eigendecompositions, the Gaussian CDF, square roots and logarithms as steps → one program of the published sampling real RAM restricted to + − × ÷, comparisons, fair coins and the sample instruction (ArithmeticCoin), chosen with one constant C before every parameter and instance, whose output has the stated guarantee and whose samples and work obey the stated bounds on every coin tape and sample stream; reason: this is the reading of the published goal Theorem 1.3 of the same paper; admitting a unit-cost eigensolver, CDF, square root or logarithm would make the existence of the routine a weaker claim, and the conclusion here is an inequality with a positive error, which an approximate computation of those steps can meet
--   - reading: "fresh samples (X, U X̃^{⊗r}, Y_max)" for both parts, while the odd features (108) contain X̃_ℓ = X_ℓ + iX′_ℓ → part (i): samples (X, Re U X̃^{⊗r}, Im U X̃^{⊗r}, Y_max); part (ii): samples (X, X′, Re U X̃^{⊗s}, Im U X̃^{⊗s}, Y_max); reason: Algorithm 8.1 takes features "evaluated from the supplied samples", and the odd features cannot be evaluated without X′; part (i) is stated for the printed triple
--   - reading: running time at most poly(n, k, p, 1/ε_est, log(1/δ)) → work at most C·(n + k + p + 1/ε_est + log(1/δ))^{C·K^C}; reason: the sample count already contains 100^s = n^{Θ(K⁴)}, so the degree of the polynomial depends on K; B and ∆ are "absolute constants" in Assumption 1.2, and the dependence on K is made explicit instead of hidden
--   - encoding: Õ((p²n/ε_est²) 100^s log(1/δ)) projected samples → C·(p²n/ε_est²)·100^s·(1 + log(np/ε_est))^C·log(1/δ) with one natural number C; reason: Õ hides a power of the logarithm of the size parameters
--   - encoding: U is fixed, with n^r columns; returned matrices; part (ii) "at r = s" → U enters only through the law of the samples and is not an input of the program; outputs are read from memory; part (ii) is stated for U ∈ ℝ^{p×n^s} outside the quantifier over r; reason: conventions; an input with n^r entries could not be read within the stated time
--   - encoding: a set R̂ ⊆ ℝⁿ of recovered regressors with a bijection match : R̂ → R ⊊ [k] → estimates indexed by positions 1, …, m with m < k and an injective index map; the program receives m and the estimates, not the matching; reason: same instances (accurate estimates of distinct regressors are distinct); the order of the list carries no information about the matching
--   - encoding: s := K⁴ log n (Hyperparameters 4.1), used as a tensor order → s = ⌈K⁴ log n⌉ (the published hypS); reason: the convention of the published base mission; (182) states s ≤ 2K⁴ log n
-- source:
--   Zhou, Linear Regression with Self-Selection Bias in Polynomial Time, STOC 2027 submission (manuscript sha256 5d65f750…), Theorem 8.1, p.55 (PDF p.58); Algorithm 8.1, p.57 (PDF p.60); features (107), (108), pp.56–57 (PDF pp.59–60)

import Mathlib
import Definitions.Def_GaussMixHH_Machine
import Definitions.Def_SelfSelReg_SatisfiesAssumption
import Definitions.Def_SelfSelReg_ArithmeticCoin
import Definitions.Def_SelfSelReg_hypK
import Definitions.Def_SelfSelReg_Tensor
import Definitions.Def_SelfSelReg_restrictedMoment
import Definitions.Def_SelfSelReg_Supplement_RecoveredList
import Definitions.Def_SelfSelReg_Supplement_Routine
import Definitions.Def_SelfSelReg_Supplement_ProjectedMoments
import Definitions.Def_SelfSelReg_Supplement_ProjectedSample

open MeasureTheory ProbabilityTheory

namespace SelfSelReg

namespace Supplement

/-- **Theorem 8.1** (Hermite Moment Estimation by Peeling), parts (i) and (ii).

F. Zhou, *Linear Regression with Self-Selection Bias in Polynomial Time*, STOC 2027 submission
(manuscript sha256 5d65f750…), Theorem 8.1, p.55 (PDF p.58); Algorithm 8.1, p.57 (PDF p.60):
"Consider the Gaussian self-selection model (Definition 1.1) under the boundedness and uncoveredness
assumptions (Assumption 1.2). Use the hyperparameters K, T, s from Hyperparameters 4.1. Let 2 ≤ r ≤ s,
and fix a projection map U : ℝ^{n^r} → ℝᵖ, where U ∈ ℝ^{p×n^r} has orthonormal rows. Assume we are given
fresh samples (X, U X̃^{⊗r}, Y_max) where X̃ = X + iX′. Fix a sampling accuracy ε_est ∈ (0, 1) and a
failure probability δ ∈ (0, 1/3). Let R̂ be a set of regressor estimates matched to some R ⊊ [k], and
put Q = [k] ∖ R. If the estimates satisfy ‖ŵ − w_match(ŵ)‖₂ ≤ e^{−K⁶s} (ŵ ∈ R̂), then the following
guarantees hold. (i) For the projected even moment at order r, ESTIMATEMOMENTSBYPEELING (Algorithm
8.1), given sampling accuracy ε_est and confidence parameter δ, returns a symmetric matrix
M̂ ∈ ℝ^{p×p} satisfying, with probability at least 1 − δ,
‖M̂ − U Mat_r(T^Q_{2r})Uᵀ‖_F ≤ ε_est + (√k/√(2π))e^{−K⁶s} + e^{4s log K − T²/(2K)} k tr(A^{(r)}_Q) (101).
(ii) For the projected odd moment at r = s, ESTIMATEMOMENTSBYPEELING returns symmetric matrices
M̂_1, …, M̂_n ∈ ℝ^{p×p} satisfying, with probability at least 1 − δ, simultaneously for every b ∈ ℝⁿ,
‖Σ_ℓ b_ℓ M̂_ℓ − U Mat_s(T^Q_{2s+1} ⌟ b)Uᵀ‖_F ≤ (ε_est + (√k/√(2π))e^{−K⁶s} +
e^{4s log K − T²/(2K)} k tr(A^{(s)}_Q))‖b‖₂ (102). Each call requires at most
Õ((p²n/ε_est²) 100^s log(1/δ)) projected samples. Moreover, its running time is at most
poly(n, k, p, 1/ε_est, log(1/δ))."

**Formalization Note.**
* The routine is one program `P` of the published sampling real RAM, restricted by `ArithmeticCoin`,
  chosen with the constant `C` before every parameter and instance, as in the published goal. Its
  input list is a mode (`0` even, `1` odd), then `n, k, p, r, B, ∆, ε_est, δ, |R̂|`, then the estimates
  of `R̂`. The map `U` (which has `n^r` columns) is not an input: it enters only through the law of
  the samples. `K, T, s` are the published `hypK`, `hypT`, `hypS`; `T^Q_d` is the published
  `restrictedMoment`, `A^{(r)}_Q` the published `evenTarget`.
* (i): one `sample` writes one projected sample `(X, U X̃^{⊗r}, Y_max) ∈ ℝ^{n+2p+1}`
  (`projectedSampleLaw`). (ii): the odd features (108) contain `X̃_ℓ`, so one `sample` writes
  `(X, X′, U X̃^{⊗s}, Y_max) ∈ ℝ^{2n+2p+1}` (`projectedSampleLawOdd`).
* Output: `M̂` is `decodeMat p 0`; `M̂_ℓ` is `decodeMat p ℓ` for `ℓ = 0, …, n − 1`. They are
  symmetric on every run. In (ii) the event of probability at least `1 − δ` is one event, on which the
  bound holds for every `b`.
* `Õ((p²n/ε_est²) 100^s log(1/δ))` is `C (p²n/ε_est²) 100^s (1 + log(np/ε_est))^C log(1/δ)`.
  "poly(n, k, p, 1/ε_est, log(1/δ))" is `C (n + k + p + 1/ε_est + log(1/δ))^{C K^C}`: the sample count
  already contains `100^s = n^{Θ(K⁴)}`, so the degree of the polynomial depends on `K` (`B, ∆` are
  "absolute constants" in Assumption 1.2). All bounds hold on **every** coin tape and sample stream. -/
theorem theorem_8_1 :
    ∃ (P : GaussMixHH.Program) (_ : GaussMixHH.Admissible P) (_ : ArithmeticCoin P) (C : ℕ),
      ∀ (n k p : ℕ), 2 ≤ k → k ≤ n → 1 ≤ p →
      ∀ (B Δ εest δ : ℝ), 1 ≤ B → 0 < Δ → Δ ≤ 1 → 0 < εest → εest < 1 → 0 < δ → δ < 1 / 3 →
      ∀ w : Fin k → EuclideanSpace ℝ (Fin n), SatisfiesAssumption B Δ w →
      ∀ Rhat : RecoveredList n k,
        Rhat.Accurate w (Real.exp (-(hypK B Δ ^ 6 * hypS B Δ n))) →
        (∀ (r : ℕ), 2 ≤ r → r ≤ hypS B Δ n →
          ∀ U : Matrix (Fin p) (Fin r → Fin n) ℝ, HasOrthonormalRows U →
          RandomizedRoutine P
            ([0, (n : ℝ), (k : ℝ), (p : ℝ), (r : ℝ), B, Δ, εest, δ, (Rhat.size : ℝ)] ++ Rhat.data)
            (projectedSampleLaw w U) δ
            (C * ((p : ℝ) ^ 2 * n / εest ^ 2) * (100 : ℝ) ^ hypS B Δ n *
              (1 + Real.log ((n : ℝ) * p / εest)) ^ C * Real.log (1 / δ))
            (C * ((n : ℝ) + k + p + 1 / εest + Real.log (1 / δ)) ^ ((C : ℝ) * hypK B Δ ^ C))
            (fun st => (decodeMat p 0 st).IsHermitian)
            (fun st =>
              matFrobNorm (decodeMat p 0 st -
                U * matFlat r (restrictedMoment w (hypT B Δ n) Rhat.remaining (2 * r)) *
                  U.transpose) ≤
                εest + Real.sqrt k / Real.sqrt (2 * Real.pi) *
                    Real.exp (-(hypK B Δ ^ 6 * hypS B Δ n)) +
                  Real.exp (4 * hypS B Δ n * Real.log (hypK B Δ) -
                      hypT B Δ n ^ 2 / (2 * hypK B Δ)) * k *
                    Matrix.trace (evenTarget w (hypT B Δ n) Rhat.remaining r))) ∧
        (∀ U : Matrix (Fin p) (Fin (hypS B Δ n) → Fin n) ℝ, HasOrthonormalRows U →
          RandomizedRoutine P
            ([1, (n : ℝ), (k : ℝ), (p : ℝ), (hypS B Δ n : ℝ), B, Δ, εest, δ, (Rhat.size : ℝ)] ++
              Rhat.data)
            (projectedSampleLawOdd w U) δ
            (C * ((p : ℝ) ^ 2 * n / εest ^ 2) * (100 : ℝ) ^ hypS B Δ n *
              (1 + Real.log ((n : ℝ) * p / εest)) ^ C * Real.log (1 / δ))
            (C * ((n : ℝ) + k + p + 1 / εest + Real.log (1 / δ)) ^ ((C : ℝ) * hypK B Δ ^ C))
            (fun st => ∀ l : Fin n, (decodeMat p l st).IsHermitian)
            (fun st => ∀ b : EuclideanSpace ℝ (Fin n),
              matFrobNorm ((∑ l : Fin n, b l • decodeMat p l st) -
                U * matFlat (hypS B Δ n)
                    (contractLast (restrictedMoment w (hypT B Δ n) Rhat.remaining
                      (2 * hypS B Δ n + 1)) b) *
                  U.transpose) ≤
                (εest + Real.sqrt k / Real.sqrt (2 * Real.pi) *
                    Real.exp (-(hypK B Δ ^ 6 * hypS B Δ n)) +
                  Real.exp (4 * hypS B Δ n * Real.log (hypK B Δ) -
                      hypT B Δ n ^ 2 / (2 * hypK B Δ)) * k *
                    Matrix.trace (evenTarget w (hypT B Δ n) Rhat.remaining (hypS B Δ n))) *
                  ‖b‖)) := by sorry

end Supplement

end SelfSelReg
