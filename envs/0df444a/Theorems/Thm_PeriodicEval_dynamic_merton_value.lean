-- Prove2me | Theorems.Thm_PeriodicEval_dynamic_merton_value
-- name    : PeriodicEval.dynamic_merton_value
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:09:03.030572+00:00
-- url     : https://prove2.me/theorems/d0b29234-6b2d-44e9-89ae-f2611177b744
-- title:
--   Proof of Proposition 1, p.42 — the dynamic Merton value $\sup_{X\in\mathcal A_0(x)}E[X_T^\alpha]=x^\alpha e^{hT}$
-- statement:
--   Under the standing assumptions, for every $x>0$ and every horizon $T\ge0$,
--
--   $$\sup_{X\in\mathcal A_0(x)}E[X_T^\alpha]=x^\alpha\exp\Big(\Big(r\alpha+\frac{(\mu-r)^2}{2\sigma^2}\frac{\alpha}{1-\alpha}\Big)T\Big)=x^\alpha e^{hT}.$$
--
--   In particular $\sup_{X\in\mathcal A_0(x)}E[X^\alpha_{T_i}]=x^\alpha e^{i\tau h}$. This is the value of the finite-horizon Merton problem with power utility; it bounds the positive part of the objective (Proposition 1) and the remainder term in the verification of Theorem 1.
--
--   Differences from the source:
--   - generalization: maturity T_i = iτ, value x^α e^{iτh} → every horizon T ≥ 0, value x^α e^{hT}; reason: T = T_i gives the paper's identity; the proof of Theorem 1 uses it at T_n
--   - encoding: sup_{X ∈ A_0(x)} E[X^α_{T_i}] as a real or extended-real supremum → sSup in EReal; reason: an unbounded set gives ⊤ instead of a junk real value; on bounded sets the value is the paper's
-- source:
--   Tse–Zheng, Portfolio Selection, Periodic Evaluations and Risk Taking, SSRN 3971852 (June 20, 2023), proof of Proposition 1, p.42 (also used in the proof of Theorem 1, p.43)

import Mathlib
import Definitions.Def_PeriodicEval_Objective
import Definitions.Def_PeriodicEval_Auxiliary

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace PeriodicEval

/-- The dynamic Merton value, SSRN 3971852 (June 20, 2023), proof of Proposition 1, p.42:
"`sup_{X ∈ A_0(x)} E[X^α_{T_i}]` is simply the value function of a finite horizon Merton
investment problem with power utility function, maturity `T_i` and initial wealth of `x`",
`sup_{X ∈ A_0(x)} E[X^α_{T_i}] = x^α exp((rα + ((μ − r)²/(2σ²))(α/(1 − α))) T_i) = x^α e^{iτh}`.

Stated for every horizon `T ≥ 0` (value `x^α e^{hT}`), which contains the paper's `T = T_i`.

**Formalization Note** The supremum is in `EReal`. `X_T ≥ 0` almost surely for admissible `X`,
so `X_T^α` is the usual power almost surely. -/
theorem dynamic_merton_value (p : Params) (hp : p.Standing) {Ω : Type*} [m : MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (B : ℝ≥0 → Ω → ℝ) (hB : IsBrownianReal B P)
    (ℱ : Filtration ℝ≥0 m) (hℱ : IsAugmentedNaturalFiltration P B ℱ) (x : ℝ) (hx : 0 < x) (T : ℝ≥0) :
    sSup {z : EReal | ∃ X ∈ admissible p P ℱ B 0 x,
        z = ((∫ ω, X T ω ^ p.α ∂P : ℝ) : EReal)} =
      ((x ^ p.α * Real.exp (p.h * (T : ℝ)) : ℝ) : EReal) := by sorry

end PeriodicEval
