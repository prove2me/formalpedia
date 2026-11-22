-- Prove2me | Theorems.Thm_SelfSelReg_Supplement_theorem_7_1
-- name    : SelfSelReg.Supplement.theorem_7_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-22T05:20:53.753118+00:00
-- url     : https://prove2.me/theorems/31ee03be-1ef3-444b-8f80-a4b841234990
-- title:
--   Theorem 7.1 — restricted least-squares refinement
-- statement:
--   Consider the Gaussian self-selection model with regressors $w_1,\dots,w_k\in\mathbb R^n$, $2\le k\le n$, under Assumption 1.2 with constants $B\ge1$, $\Delta\in(0,1]$, and let $K=16(1+B^2)^3/\Delta^4$. Fix $\varepsilon\in(0,1)$, $\delta\in(0,1/3)$ and $i\in[k]$. Suppose the unit vector $\widehat u\in\mathbb R^n$ satisfies
--
--   $$
--   \Bigl\|\widehat u-\frac{w_i}{\|w_i\|_2}\Bigr\|_2\le\frac{\Delta^2}{16B^2}.
--   $$
--
--   Then RESTRICTEDLEASTSQUARES (Algorithm 7.1), given $\widehat u$, $\varepsilon$, $\delta$ and sample access to $(X,Y_{\max})$, returns an estimate $\widehat w$ satisfying
--
--   $$
--   \|\widehat w-w_i\|_2\le\varepsilon
--   $$
--
--   with probability at least $1-\delta$. Its sample complexity is $\widetilde O\bigl((nk/\varepsilon)^{5K^2}\log(1/\delta)\bigr)$ and its running time is $\widetilde O\bigl((nk/\varepsilon)^{\mathrm{poly}(K)}\log(1/\delta)\bigr)$.
--
--   The theorem turns a rough direction, as produced by the tensor decomposition of Theorem 6.1, into an estimate of the full regressor, norm included, to any accuracy.
--
--   **Formalization Note** The routine is a program of the sampling real RAM of the base mission, restricted to exact arithmetic, comparisons, fair coins and sample reads, fixed with one constant $C$ before all parameters. The bounds are $C(nk/\varepsilon)^{5K^2}\log(nk/\varepsilon)^C\log(1/\delta)$ samples and $C(nk/\varepsilon)^{CK^C}\log(1/\delta)$ work on every run; the exponent $5K^2$ is exact.
--
--   Differences from the source:
--
--   - reading: "RESTRICTEDLEASTSQUARES (Algorithm 7.1) returns …", "its sample complexity is …", "its running time is …", with no machine named; the pseudocode uses exact eigendecompositions, the Gaussian CDF, square roots and logarithms as steps → one program of the published sampling real RAM restricted to + − × ÷, comparisons, fair coins and the sample instruction (ArithmeticCoin), chosen with one constant C before every parameter and instance, whose output has the stated guarantee and whose samples and work obey the stated bounds on every coin tape and sample stream; reason: this is the reading of the published goal Theorem 1.3 of the same paper; admitting a unit-cost eigensolver, CDF, square root or logarithm would make the existence of the routine a weaker claim, and the conclusion here is an inequality with a positive error, which an approximate computation of those steps can meet
--   - encoding: Õ((nk/ε)^{5K²} log(1/δ)) samples and Õ((nk/ε)^{poly(K)} log(1/δ)) time → C(nk/ε)^{5K²}·log(nk/ε)^C·log(1/δ) samples and C(nk/ε)^{C·K^C}·log(1/δ) work with one natural number C, natural logarithm; reason: Õ hides a power of log(nk/ε); in the time bound it is absorbed by the exponent since nk/ε ≥ 4
--   - encoding: the statement begins "Fix ε ∈ (0, 1), δ ∈ (0, 1/3), and i ∈ [k]"; the model, Assumption 1.2 and K are those of the paper → explicit hypotheses 2 ≤ k ≤ n, B ≥ 1, ∆ ∈ (0, 1], Assumption 1.2, K the published hypK; reason: standing setting of the paper (Definition 1.1, Assumption 1.2, Hyperparameters 4.1)
-- source:
--   Zhou, Linear Regression with Self-Selection Bias in Polynomial Time, STOC 2027 submission (manuscript sha256 5d65f750…), Theorem 7.1, pp.48–49 (PDF pp.51–52); Algorithm 7.1, p.49 (PDF p.52)

import Mathlib
import Definitions.Def_GaussMixHH_Machine
import Definitions.Def_SelfSelReg_SatisfiesAssumption
import Definitions.Def_SelfSelReg_sampleLaw
import Definitions.Def_SelfSelReg_ArithmeticCoin
import Definitions.Def_SelfSelReg_hypK
import Definitions.Def_SelfSelReg_restrictedMoment
import Definitions.Def_SelfSelReg_Supplement_Routine

open MeasureTheory ProbabilityTheory

namespace SelfSelReg

namespace Supplement

/-- **Theorem 7.1** (Restricted Least-Squares Refinement).

F. Zhou, *Linear Regression with Self-Selection Bias in Polynomial Time*, STOC 2027 submission
(manuscript sha256 5d65f750…), Theorem 7.1, pp.48–49 (PDF pp.51–52); Algorithm 7.1, p.49
(PDF p.52): "Fix ε ∈ (0, 1), δ ∈ (0, 1/3), and i ∈ [k]. Suppose the unit vector û satisfies
‖û − w_i/‖w_i‖₂‖₂ ≤ ∆²/(16B²). Then RESTRICTEDLEASTSQUARES (Algorithm 7.1) returns an estimate ŵ
satisfying ‖ŵ − w_i‖₂ ≤ ε (86) with probability at least 1 − δ. Its sample complexity is
Õ((nk/ε)^{5K²} log(1/δ)) and its running time is Õ((nk/ε)^{poly(K)} log(1/δ))."

**Formalization Note.**
* The setting is the paper's: the model of Definition 1.1 with `2 ≤ k ≤ n` under Assumption 1.2, and
  `K` the published `hypK B ∆`.
* The routine is one program `P` of the published sampling real RAM, restricted by `ArithmeticCoin`,
  chosen with the constant `C` before every parameter and instance, as in the published goal. It runs
  in dimension `n + 1`, receives `k, B, ∆, ε, δ` and the coordinates of `û`, and reads observations
  `(X, Y_max)` by `sample`. The output `ŵ` is `decodeVec n 0`.
* `Õ((nk/ε)^{5K²} log(1/δ))` is `C (nk/ε)^{5K²} log(nk/ε)^C log(1/δ)`: the exponent `5K²` is exact
  and `Õ` hides a power of `log(nk/ε)`. `Õ((nk/ε)^{poly(K)} log(1/δ))` is
  `C (nk/ε)^{C K^C} log(1/δ)` (logarithmic factors are absorbed by the exponent). Both hold on
  **every** coin tape and sample stream. -/
theorem theorem_7_1 :
    ∃ (P : GaussMixHH.Program) (_ : GaussMixHH.Admissible P) (_ : ArithmeticCoin P) (C : ℕ),
      ∀ (n k : ℕ), 2 ≤ k → k ≤ n →
      ∀ (B Δ ε δ : ℝ), 1 ≤ B → 0 < Δ → Δ ≤ 1 → 0 < ε → ε < 1 → 0 < δ → δ < 1 / 3 →
      ∀ w : Fin k → EuclideanSpace ℝ (Fin n), SatisfiesAssumption B Δ w →
      ∀ (i : Fin k) (uhat : EuclideanSpace ℝ (Fin n)), ‖uhat‖ = 1 →
        ‖uhat - unitReg w i‖ ≤ Δ ^ 2 / (16 * B ^ 2) →
        RandomizedRoutine P
          ([(k : ℝ), B, Δ, ε, δ] ++ vecData uhat)
          (sampleLaw w) δ
          (C * ((n : ℝ) * k / ε) ^ (5 * hypK B Δ ^ 2) * Real.log ((n : ℝ) * k / ε) ^ C *
            Real.log (1 / δ))
          (C * ((n : ℝ) * k / ε) ^ ((C : ℝ) * hypK B Δ ^ C) * Real.log (1 / δ))
          (fun _ => True)
          (fun st => ‖decodeVec n 0 st - w i‖ ≤ ε) := by sorry

end Supplement

end SelfSelReg
