-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P29_global_contractivity
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P29.global_contractivity
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T05:06:29.914208+00:00
-- url     : https://prove2.me/theorems/87769870-7180-4885-a925-609ecde04775
-- title:
--   Theorem 2 (17): contractivity of Sb under global wirings
-- statement:
--   All Bell scenarios have independent finite, nonempty Alice and Bob input and output alphabets. A behavior is a nonnegative conditional output law normalized at every input pair; $\mathrm{NS}$ imposes both no-signaling marginal identities. Processing uses one initial box with rules and randomness fixed independently of the supplied behavior. Write $D(P\Vert Q)$ for classical Kullback–Leibler divergence with natural logarithms, zero numerator contributing zero and positive numerator over zero contributing $+\infty$. Define $S_b(P\Vert Q)=\max_{x,y}D(P(\cdot,\cdot\mid x,y)\Vert Q(\cdot,\cdot\mid x,y))$. For every pair $P,Q\in\mathrm{NS}$ with the same alphabets and every global wiring $G$ between arbitrary scenarios,
--
--   $$S_b(G(P)\Vert G(Q))\le S_b(P\Vert Q).$$
--
--   The input and output processing kernels of $G$ are arbitrary normalized kernels. Its output behaviors may be signaling. This is data processing for the maximized conditional-output divergence.
-- source:
--   Nonlocality free wirings and the distinguishability between Bell boxes, arXiv:1611.06932v2, PDF p. 5, Theorem 2 (17)

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

/-- PDF p.5, Theorem 2, (17), proved on pp.11–12. The two input boxes are NS;
GW output boxes are allowed to be signaling. -/
theorem global_contractivity {s t : BellScenario} (g : GlobalWiring s t)
    (p q : Behavior s) (hp : IsNS p) (hq : IsNS q) :
    sb (g.apply p) (g.apply q) ≤ sb p q := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P29

end
