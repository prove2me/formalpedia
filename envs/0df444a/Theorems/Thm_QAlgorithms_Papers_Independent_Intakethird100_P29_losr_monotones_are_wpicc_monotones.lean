-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P29_losr_monotones_are_wpicc_monotones
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P29.losr_monotones_are_wpicc_monotones
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T05:08:15.66872+00:00
-- url     : https://prove2.me/theorems/af62b6ba-2348-4b65-aa6a-3345fd052c78
-- title:
--   Lemma 6: LOSR monotones are WPICC monotones
-- statement:
--   All Bell scenarios have independent finite, nonempty Alice and Bob input and output alphabets. A behavior is a nonnegative conditional output law normalized at every input pair; $\mathrm{NS}$ imposes both no-signaling marginal identities. Processing uses one initial box with rules and randomness fixed independently of the supplied behavior. A Bell nonlocality monotone is a family of finite, nonnegative values on no-signaling behaviors in all scenarios. It vanishes on every local behavior and does not increase under LOSR or WPICC operations, including operations changing alphabet sizes. For every such nonnegative real-valued family $f$, LOSR monotonicity implies WPICC monotonicity:
--
--   $$f\text{ is an LOSR monotone}\ \Longrightarrow\ f\text{ is a WPICC monotone}.$$
--
--   There is no convexity or continuity assumption. This identifies the two choices of free-operation class for nonlocality monotones. WPICC uses Appendix A’s fixed no-preparation LOSR branch and random adaptive preparation branches in which at least one party measures before the final inputs.
-- source:
--   Nonlocality free wirings and the distinguishability between Bell boxes, arXiv:1611.06932v2, PDF p. 6, Lemma 6

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

/-- PDF p.6, Lemma 6. No convexity, continuity, or positivity-on-nonlocal-boxes
premise is imposed on the nonnegative real-valued family. -/
theorem losr_monotones_are_wpicc_monotones (f : Quantity)
    (hf : IsLOSRMonotone f) : IsWPICCMonotone f := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P29

end
