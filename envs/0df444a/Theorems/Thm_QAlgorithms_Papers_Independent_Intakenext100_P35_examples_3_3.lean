-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P35_examples_3_3
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P35.examples_3_3
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T05:13:21.071648+00:00
-- url     : https://prove2.me/theorems/2a0f2fdd-a0da-4ac7-9cd1-a5a62309538a
-- title:
--   Examples 3.3
-- statement:
--   The symbol $e^{-1/z}$ fails to belong to $\mathcal B$ because it is not uniformly continuous near zero, although $z(1+z)^{-1}e^{-1/z}$ belongs to $\mathcal{LM}$. The branch $\operatorname{arccot}z=(2i)^{-1}\log((z+i)/(z-i))$ is unbounded; its exponential is bounded but not uniformly continuous near $i$, so neither belongs to $\mathcal B$. Finally,
--
--   $$e^{-z}(1+z)^i,\qquad e^{-2z}\int_0^1\frac{\sinh(zt)}t\,dt$$
--
--   belong to $\mathcal B\setminus\mathcal{LM}$. These examples distinguish the symbol classes.
-- source:
--   Bounded functional calculi for unbounded operators, arXiv:2202.03143v1, PDF p. 7, Examples 3.3

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P35

noncomputable section

open Complex MeasureTheory Filter Set

open scoped Topology ENNReal

namespace QAlgorithms.Papers.Independent.Intakenext100.P35

open QAlgorithms.Papers.Independent.Renew46.P11 (HolomorphicBernstein)

attribute [local instance] Classical.propDecidable

universe u

/-- Examples 3.3, arXiv:2202.03143v1, PDF page(s) 7, 8. -/
theorem examples_3_3
:
    (¬ BesovClass (fun z => Complex.exp (-1 / z))) ∧
    (¬ ∃ r : ℝ, 0 < r ∧ UniformContinuousOn (fun z => Complex.exp (-1 / z))
      (hp ∩ Metric.ball 0 r)) ∧
    LM (phiSymbol 1) ∧
    (¬ HInfinity hp arccot) ∧ (¬ BesovClass arccot) ∧
    HInfinity hp (fun z => Complex.exp (arccot z)) ∧
    (¬ BesovClass (fun z => Complex.exp (arccot z))) ∧
    (¬ ∃ r : ℝ, 0 < r ∧ UniformContinuousOn (fun z => Complex.exp (arccot z))
      (hp ∩ Metric.ball Complex.I r)) ∧
    BesovClass (fun z => Complex.exp (-z) * (1 + z) ^ Complex.I) ∧
    (¬ LM (fun z => Complex.exp (-z) * (1 + z) ^ Complex.I)) ∧
    BesovClass (fun z => Complex.exp (-2 * z) * ∫ t in Icc (0 : ℝ) 1, sinhQuotient z t) ∧
    (¬ LM (fun z => Complex.exp (-2 * z) * ∫ t in Icc (0 : ℝ) 1, sinhQuotient z t)) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P35

end
