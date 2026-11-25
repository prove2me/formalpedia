-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_withBot_le_one_of_le_two_20da161cf909
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_withBot_le_one_of_le_two_20da161cf909
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T08:03:26.174715+00:00
-- url     : https://prove2.me/theorems/fdd36b99-ea00-538b-b40f-5eba482492aa
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman with Bot le one of le two 20da161cf909: P2 M Ground Theory Heights  Heights Kleiman with Bot le one of le two 20da161cf909
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman with Bot le one of le two 20da161cf909 construction uses the P2 M Ground Theory Heights  Heights Kleiman with Bot le one of le two 20da161cf909 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PCycleSplit.lean#L59-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PCycleSplit.lean#L59-L71

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsCycleSplit
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsCycleSplitFilt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsCycleSplitCurve
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsCycleSplitSmall
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PCycleSplit
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial Filter
universe u w
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ} {x : Fin (N + 1) → Ω}

theorem P2M_GroundTheory_Heights__Heights_Kleiman_withBot_le_one_of_le_two_20da161cf909 {a : WithBot ℕ∞} (h2 : a ≤ 2)
    (hne : a ≠ ((1 + 1 : ℕ) : WithBot ℕ∞)) : a ≤ 1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«withBot_le_one_of_le_two» := P2M_GroundTheory_Heights__Heights_Kleiman_withBot_le_one_of_le_two_20da161cf909
