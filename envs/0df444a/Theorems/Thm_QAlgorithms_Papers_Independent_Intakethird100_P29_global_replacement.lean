-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P29_global_replacement
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P29.global_replacement
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T05:15:05.038638+00:00
-- url     : https://prove2.me/theorems/e915cf9a-d557-46c3-bddc-dd45c1e4399c
-- title:
--   Unnumbered result: a GW can convert any behavior into any other
-- statement:
--   All Bell scenarios have independent finite, nonempty Alice and Bob input and output alphabets. A behavior is a nonnegative conditional output law normalized at every input pair; $\mathrm{NS}$ imposes both no-signaling marginal identities. Processing uses one initial box with rules and randomness fixed independently of the supplied behavior. For any normalized initial behavior $P$ and any normalized target behavior $Q$, on possibly different scenarios, there exists a global wiring $G$ such that
--
--   $$G(P)=Q.$$
--
--   Both behaviors may be signaling. The operation may depend on the chosen target, as in the source’s constant-output-kernel construction.
-- source:
--   Nonlocality free wirings and the distinguishability between Bell boxes, arXiv:1611.06932v2, PDF p. 4, Unnumbered result after (11)

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

/-- PDF p.4, after (11): arbitrary normalized behaviors, including signaling
ones, can be replaced by a target-dependent GW. -/
theorem global_replacement {s t : BellScenario} (p : Behavior s) (q : Behavior t)
    (hp : IsCorrelation p) (hq : IsCorrelation q) :
    ∃ g : GlobalWiring s t, g.apply p = q := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P29

end
