-- Prove2me | Theorems.Thm_P2M_GlobalTheory_FullLevel_M_dvd_M__ccc9399a2d7f
-- name    : P2M_GlobalTheory_FullLevel_M_dvd_M__ccc9399a2d7f
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T20:18:24.766872+00:00
-- url     : https://prove2.me/theorems/2590b83b-c6c8-407c-bbb6-0bdb440254e8
-- title:
--   P2 M Global Theory Full Level M dvd M  ccc9399a2d7f: P2 M Global Theory Full Level M dvd M  ccc9399a2d7f
-- statement:
--   The P2 M Global Theory Full Level M dvd M  ccc9399a2d7f construction uses the P2 M Global Theory Full Level M dvd M  ccc9399a2d7f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsSympLevel.lean#L27-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsSympLevel.lean#L27-L27

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_PushInvertible
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_AbelianLawCounterexamples_WeilIsUniqueOfLocal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsSympLevel
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.FullLevel
open ReciprocityTheory.ChartRestriction.G.Geo.Tor NumberField
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem P2M_GlobalTheory_FullLevel_M_dvd_M__ccc9399a2d7f (l : Level H) : l.M ∣ l.M' := by sorry

alias «GlobalTheory».«FullLevel».«M_dvd_M'» := P2M_GlobalTheory_FullLevel_M_dvd_M__ccc9399a2d7f
