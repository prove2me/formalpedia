-- Prove2me | Theorems.Thm_SelfSelReg_Supplement_theorem_6_1
-- name    : SelfSelReg.Supplement.theorem_6_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-22T05:17:57.505776+00:00
-- url     : https://prove2.me/theorems/dd20dcba-b454-4cb8-b1c0-8a4f2490f5ee
-- title:
--   Theorem 6.1 — implicit tensor decomposition
-- statement:
--   Consider the Gaussian self-selection model with regressors $w_1,\dots,w_k\in\mathbb R^n$, $2\le k\le n$, satisfying the boundedness and uncoveredness conditions (Assumption 1.2) with constants $B\ge1$ and $\Delta\in(0,1]$, and let $K=16(1+B^2)^3/\Delta^4$ and $s=\lceil K^4\log n\rceil$ be the hyperparameters of the paper. Let $\widehat{\mathcal R}$ be a recovered list matched bijectively to $R\subsetneq[k]$ with
--
--   $$
--   \|\widehat w-w_{\mathrm{match}(\widehat w)}\|_2\le e^{-K^6s}\qquad(\widehat w\in\widehat{\mathcal R}),
--   $$
--
--   and put $Q=[k]\setminus R$. Given $\widehat{\mathcal R}$, a confidence parameter $\delta\in(0,1/3)$ and fresh samples $(X,Y_{\max})$ independent of $\widehat{\mathcal R}$, the routine IMPLICITTENSORDECOMPOSITION returns unit vectors $\widehat u_1,\dots,\widehat u_{i_\star}$ with $1\le i_\star\le|Q|$ such that, with probability at least $1-\delta$, there is an injection $\pi:[i_\star]\to Q$ with
--
--   $$
--   \max_{\ell\in[i_\star]}\Bigl\|\widehat u_\ell-\frac{w_{\pi(\ell)}}{\|w_{\pi(\ell)}\|_2}\Bigr\|_2\le e^{-s/(2K)}\le\frac{\Delta^2}{16B^2}.
--   $$
--
--   Its sample complexity is $\widetilde O\bigl((nk)^{O(K^{10})}\log(1/\delta)\bigr)$ and its running time is $(nk)^{\mathrm{poly}(K)}\log(1/\delta)$.
--
--   This is the tensor-decomposition step of the main algorithm: each call produces rough directions of at least one regressor not yet recovered, accurate enough to start the least-squares refinement of Theorem 7.1.
--
--   **Formalization Note** The routine is a program of the sampling real RAM of the base mission, restricted to exact arithmetic, comparisons, fair coins and sample reads; it and one constant $C$ are fixed before all parameters. The resource bounds are $C(nk)^{CK^{10}}\log(1/\delta)$ samples and $C(nk)^{CK^{C}}\log(1/\delta)$ work on every run. The count $i_\star$ and the unit norm of the outputs hold on every run; the injection exists on an event of probability at least $1-\delta$. The inequality $e^{-s/(2K)}\le\Delta^2/(16B^2)$ is a separate conjunct.
--
--   Differences from the source:
--
--   - reading: "IMPLICITTENSORDECOMPOSITION (Algorithm 6.4) returns …", "its sample complexity is …", "its running time is …", with no machine named; the pseudocode uses exact eigendecompositions, the Gaussian CDF, square roots and logarithms as steps → one program of the published sampling real RAM restricted to + − × ÷, comparisons, fair coins and the sample instruction (ArithmeticCoin), chosen with one constant C before every parameter and instance, whose output has the stated guarantee and whose samples and work obey the stated bounds on every coin tape and sample stream; reason: this is the reading of the published goal Theorem 1.3 of the same paper; admitting a unit-cost eigensolver, CDF, square root or logarithm would make the existence of the routine a weaker claim, and the conclusion here is an inequality with a positive error, which an approximate computation of those steps can meet
--   - encoding: Õ((nk)^{O(K¹⁰)} log(1/δ)) samples and (nk)^{poly(K)} log(1/δ) time → C(nk)^{C·K¹⁰}·log(1/δ) samples and C(nk)^{C·K^C}·log(1/δ) work with one natural number C, natural logarithm; reason: explicit constants; logarithmic factors in n, k are absorbed by the exponent since nk ≥ 4
--   - encoding: a set R̂ ⊆ ℝⁿ of recovered regressors with a bijection match : R̂ → R ⊊ [k] → estimates indexed by positions 1, …, m with m < k and an injective index map; the program receives m and the estimates, not the matching; reason: same instances (accurate estimates of distinct regressors are distinct); the order of the list carries no information about the matching
--   - encoding: s := K⁴ log n (Hyperparameters 4.1), used as a tensor order → s = ⌈K⁴ log n⌉ (the published hypS); reason: the convention of the published base mission; (182) states s ≤ 2K⁴ log n
--   - encoding: returns unit vectors û_1, …, û_{i⋆}, where 1 ≤ i⋆ ≤ |Q|; chained inequality (37) → on every run the count i⋆ (pointer register 2) satisfies 1 ≤ i⋆ ≤ |Q| and the returned vectors have norm 1; the bound by e^{−s/(2K)} holds on the success event and e^{−s/(2K)} ≤ ∆²/(16B²) is a separate conjunct; reason: output layout is a convention; the second inequality of (37) does not involve the run
-- source:
--   Zhou, Linear Regression with Self-Selection Bias in Polynomial Time, STOC 2027 submission (manuscript sha256 5d65f750…), Theorem 6.1, pp.28–29 (PDF pp.31–32); Algorithm 6.4, p.46 (PDF p.49)

import Mathlib
import Definitions.Def_GaussMixHH_Machine
import Definitions.Def_SelfSelReg_SatisfiesAssumption
import Definitions.Def_SelfSelReg_sampleLaw
import Definitions.Def_SelfSelReg_ArithmeticCoin
import Definitions.Def_SelfSelReg_hypK
import Definitions.Def_SelfSelReg_restrictedMoment
import Definitions.Def_SelfSelReg_Supplement_RecoveredList
import Definitions.Def_SelfSelReg_Supplement_Routine

open MeasureTheory ProbabilityTheory

namespace SelfSelReg

namespace Supplement

/-- **Theorem 6.1** (Implicit Tensor Decomposition).

F. Zhou, *Linear Regression with Self-Selection Bias in Polynomial Time*, STOC 2027 submission
(manuscript sha256 5d65f750…), Theorem 6.1, pp.28–29 (PDF pp.31–32); Algorithm 6.4, p.46
(PDF p.49): "Consider the Gaussian self-selection model (Definition 1.1) under the boundedness and
uncoveredness assumptions (Assumption 1.2). Suppose the recovered list R̂ is matched bijectively to
R ⊊ [k] and ‖ŵ − w_match(ŵ)‖₂ ≤ e^{−K⁶s} (ŵ ∈ R̂). Put Q = [k] ∖ R. Given fresh samples independent of R̂
and a confidence parameter δ ∈ (0, 1/3), IMPLICITTENSORDECOMPOSITION (Algorithm 6.4) returns unit vectors
û_1, …, û_{i⋆}, where 1 ≤ i⋆ ≤ |Q|, such that, with probability at least 1 − δ, there is an injection
π : [i⋆] → Q satisfying max_{ℓ∈[i⋆]} ‖û_ℓ − w_{π(ℓ)}/‖w_{π(ℓ)}‖₂‖₂ ≤ e^{−s/(2K)} ≤ ∆²/(16B²) (37). Its sample
complexity is Õ((nk)^{O(K¹⁰)} log(1/δ)), and its running time is (nk)^{poly(K)} log(1/δ)."

**Formalization Note.**
* The routine is one program `P` of the published sampling real RAM `GaussMixHH`, restricted by the
  published `ArithmeticCoin`, as in the published goal `SelfSelReg.theorem_1_3`. `P` and the constant
  `C` are chosen before every parameter and instance. `P` runs in dimension `n + 1`, receives
  `k, B, ∆, δ, |R̂|` and then the estimates of `R̂` in memory, and reaches the model only through
  `sample`, which writes one observation `(X, Y_max)`. The matching is not an input. The i.i.d. stream
  is independent of the fixed `R̂` ("fresh samples independent of R̂").
* `K, s` are the published `hypK B ∆`, `hypS B ∆ n` (Hyperparameters 4.1).
* `Õ((nk)^{O(K¹⁰)} log(1/δ))` is `C (nk)^{C K¹⁰} log(1/δ)` and `(nk)^{poly(K)} log(1/δ)` is
  `C (nk)^{C K^C} log(1/δ)`, on **every** coin tape and sample stream.
* Output: `i⋆` is pointer register `2` (`decodeCount`) and `û_ℓ` is `decodeVec n ℓ`. On every run
  `1 ≤ i⋆ ≤ |Q|` and every `û_ℓ` is a unit vector; on an event of probability at least `1 − δ` there
  is an injection `π : [i⋆] → Q` with the bound (37). The second inequality of (37) does not involve
  the run and is a separate conjunct. -/
theorem theorem_6_1 :
    ∃ (P : GaussMixHH.Program) (_ : GaussMixHH.Admissible P) (_ : ArithmeticCoin P) (C : ℕ),
      ∀ (n k : ℕ), 2 ≤ k → k ≤ n →
      ∀ (B Δ δ : ℝ), 1 ≤ B → 0 < Δ → Δ ≤ 1 → 0 < δ → δ < 1 / 3 →
      ∀ w : Fin k → EuclideanSpace ℝ (Fin n), SatisfiesAssumption B Δ w →
      ∀ Rhat : RecoveredList n k,
        Rhat.Accurate w (Real.exp (-(hypK B Δ ^ 6 * hypS B Δ n))) →
        RandomizedRoutine P
          ([(k : ℝ), B, Δ, δ, (Rhat.size : ℝ)] ++ Rhat.data)
          (sampleLaw w) δ
          (C * ((n : ℝ) * k) ^ ((C : ℝ) * hypK B Δ ^ 10) * Real.log (1 / δ))
          (C * ((n : ℝ) * k) ^ ((C : ℝ) * hypK B Δ ^ C) * Real.log (1 / δ))
          (fun st => 1 ≤ decodeCount st ∧ decodeCount st ≤ Rhat.remaining.card ∧
            ∀ l : Fin (decodeCount st), ‖decodeVec n l st‖ = 1)
          (fun st => ∃ π : Fin (decodeCount st) → Fin k, Function.Injective π ∧
            (∀ l, π l ∈ Rhat.remaining) ∧
            ∀ l : Fin (decodeCount st), ‖decodeVec n l st - unitReg w (π l)‖ ≤
              Real.exp (-(hypS B Δ n : ℝ) / (2 * hypK B Δ))) ∧
        Real.exp (-(hypS B Δ n : ℝ) / (2 * hypK B Δ)) ≤ Δ ^ 2 / (16 * B ^ 2) := by sorry

end Supplement

end SelfSelReg
