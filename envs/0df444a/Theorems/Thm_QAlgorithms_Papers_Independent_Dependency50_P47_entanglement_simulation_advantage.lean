-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P47_entanglement_simulation_advantage
-- name    : QAlgorithms.Papers.Independent.Dependency50.P47.entanglement_simulation_advantage
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T15:48:05.723742+00:00
-- url     : https://prove2.me/theorems/d0ac2170-81c3-4c2b-a09b-6232efaeb536
-- title:
--   Appendix C unnumbered main result: entanglement helps in asymptotic correlation simulation
-- statement:
--   Let $X,Y,A,B$ be binary, with $X,Y$ independent and uniform. At bias $\beta=1/\sqrt2$, prescribe the normalized conditional law
--
--   $$
--   p(a,b\mid x,y)=\begin{cases}(1+\beta)/4,&a\oplus b=xy,\\(1-\beta)/4,&a\oplus b\ne xy.\end{cases}
--   $$
--
--   For the asymptotic one-way correlation-simulation rate regions of Section 3.2,
--
--   $$
--   0\in\mathcal R^q,\qquad \exists\Delta>0\ \forall R\in\mathcal R^c:\ R\ge\Delta.
--   $$
--
--   The winning probability is $1/2+1/(2\sqrt2)$. Thus shared entanglement helps even with repeated trials and vanishing global error. The positive classical separation is the source's asserted consequence of its numerical curve; no conjectural closed-form classical cost is adopted.
-- source:
--   On Dimension Bounds for Auxiliary Quantum Systems, arXiv:1207.3911v4, PDF p. 24, Appendix C unnumbered main result: entanglement helps in asymptotic correlation simulation

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P47

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

open MeasureTheory Filter

namespace QAlgorithms.Papers.Independent.Dependency50.P47

open QAlgorithms.Papers.Independent.Information100.P27 (shannon average)

open QAlgorithms.Papers.Independent.Information100.P39 (pushLaw)

open QAlgorithms.Papers.Independent.Information100.P48 (normalize)

open QAlgorithms.Papers.Independent.Information100.P62 (IsProjection)

/-- Appendix C, PDF pp.24–26: zero entanglement-assisted cost at Tsirelson bias,
with a strictly positive classical asymptotic cost, as asserted by the source. -/
theorem entanglement_simulation_advantage (p : Law (Fin 2 × Fin 2 × Fin 2 × Fin 2))
    (hp : IsCHSHLaw (1 / Real.sqrt 2) p) :
    0 ∈ quantumRates p ∧ ∃ delta : ℝ, 0 < delta ∧ ∀ R ∈ classicalRates p, delta ≤ R := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P47

end
