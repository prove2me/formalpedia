-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P29_wpicc_not_contained_in_global
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P29.wpicc_not_contained_in_global
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T05:07:29.984662+00:00
-- url     : https://prove2.me/theorems/0d0604bb-1d75-4953-97af-e594068d5367
-- title:
--   Corollary 4 (19): WPICC is not contained in GW
-- statement:
--   All Bell scenarios have independent finite, nonempty Alice and Bob input and output alphabets. A behavior is a nonnegative conditional output law normalized at every input pair; $\mathrm{NS}$ imposes both no-signaling marginal identities. Processing uses one initial box with rules and randomness fixed independently of the supplied behavior. There exist initial and final scenarios and a WPICC wiring $W$ for which no global wiring $G$ has the same action on every no-signaling input:
--
--   $$\exists W\in\mathrm{WPICC}\quad\forall G\in\mathrm{GW}\quad\exists P\in\mathrm{NS}: W(P)\ne G(P).$$
--
--   This is non-inclusion of classes of operations on their common domain, rather than a distinction between declared domain types. WPICC uses Appendix A’s fixed no-preparation LOSR branch and random adaptive preparation branches in which at least one party measures before the final inputs.
-- source:
--   Nonlocality free wirings and the distinguishability between Bell boxes, arXiv:1611.06932v2, PDF p. 6, Corollary 4 (19)

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

/-- PDF p.6, Corollary 4, (19). Nonmembership means that no global wiring
agrees on every NS input, independently of raw extensions outside that domain. -/
theorem wpicc_not_contained_in_global :
    ∃ (s t : BellScenario) (w : BellOperation s t), IsWPICC w ∧ ¬ HasGWRestriction w := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P29

end
