-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P29_wpicc_noncontractivity
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P29.wpicc_noncontractivity
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T05:05:49.985841+00:00
-- url     : https://prove2.me/theorems/f41b54a1-96a5-4ee7-8b5d-452b139146af
-- title:
--   Theorem 3 (18): non-contractivity of Sb under WPICC; original paper seed
-- statement:
--   All Bell scenarios have independent finite, nonempty Alice and Bob input and output alphabets. A behavior is a nonnegative conditional output law normalized at every input pair; $\mathrm{NS}$ imposes both no-signaling marginal identities. Processing uses one initial box with rules and randomness fixed independently of the supplied behavior. Write $D(P\Vert Q)$ for classical Kullback–Leibler divergence with natural logarithms, zero numerator contributing zero and positive numerator over zero contributing $+\infty$. Define $S_b(P\Vert Q)=\max_{x,y}D(P(\cdot,\cdot\mid x,y)\Vert Q(\cdot,\cdot\mid x,y))$. There exist scenarios, a WPICC wiring $W$, and two behaviors $P,Q\in\mathrm{NS}$ on the initial scenario such that
--
--   $$S_b(W(P)\Vert W(Q))>S_b(P\Vert Q).$$
--
--   This separates operational box distinguishability from distinguishability obtained by fixing the two input settings before sampling outputs. The input boxes need not be nonlocal. WPICC uses Appendix A’s fixed no-preparation LOSR branch and random adaptive preparation branches in which at least one party measures before the final inputs.
-- source:
--   Nonlocality free wirings and the distinguishability between Bell boxes, arXiv:1611.06932v2, PDF p. 6, Theorem 3 (18)

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P29

noncomputable section

open scoped BigOperators ENNReal

namespace QAlgorithms.Papers.Independent.Intakethird100.P29

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Advance50.P47
  (Box IsCorrelation IsNoSignaling HasLocalModel TwoLocalBoxes losrTransform
   correlationMixture)

open QAlgorithms.Papers.Independent.Information100.P56 (IsLaw)

open QAlgorithms.Papers.Independent.Dependency50.P47 (Law)

/-- PDF p.6, Theorem 3, (18); Appendix C, pp.12–13. No nonlocality premise.
The witness may use local boxes with one Bob input. -/
theorem wpicc_noncontractivity :
    ∃ (s t : BellScenario) (w : BellOperation s t) (p q : Behavior s),
      IsWPICC w ∧ IsNS p ∧ IsNS q ∧ sb p q < sb (w p) (w q) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P29

end
