-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_CellDSq_rem_rem_comm_6b3e204c1d90
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_CellDSq_rem_rem_comm_6b3e204c1d90
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T03:28:03.848111+00:00
-- url     : https://prove2.me/theorems/2fa8d492-4001-4d41-83b9-ce814ffde8ac
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Sections Over Localization Cell DSq rem rem comm 6b3e204c1d90: P2 M Ground Theory Heights  Heights Kleiman Sections Over Localization Cell DSq rem rem comm
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Sections Over Localization Cell DSq rem rem comm 6b3e204c1d90 construction uses the P2 M Ground Theory Heights  Heights Kleiman Sections Over Localization Cell DSq rem rem comm 6b3e204c1d90 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/DoubleSumEqZero.lean#L31-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/DoubleSumEqZero.lean#L31-L40

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_ImportsBisFurther
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_DoubleSumEqZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
noncomputable section
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH
open GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.CellDSq
variable {K : Type} [Fintype K] [LinearOrder K] {ι : K → Type} [∀ k, LinearOrder (ι k)]
omit [Fintype K]

theorem P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_CellDSq_rem_rem_comm_6b3e204c1d90 (I : ∀ k, Finset (ι k)) (p q : Σ k, ι k) :
    rem (rem I p) q = rem (rem I q) p := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«SectionsOverLocalization».«CellDSq».«rem_rem_comm» := P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_CellDSq_rem_rem_comm_6b3e204c1d90
