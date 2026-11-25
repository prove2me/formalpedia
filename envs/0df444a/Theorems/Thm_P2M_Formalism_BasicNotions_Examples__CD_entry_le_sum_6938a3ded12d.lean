-- Prove2me | Theorems.Thm_P2M_Formalism_BasicNotions_Examples__CD_entry_le_sum_6938a3ded12d
-- name    : P2M_Formalism_BasicNotions_Examples__CD_entry_le_sum_6938a3ded12d
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T23:52:38.621524+00:00
-- url     : https://prove2.me/theorems/af01b6fc-6f48-4eba-982d-9f22cc47ff33
-- title:
--   P2 M Formalism Basic Notions Examples  CD entry le sum 6938a3ded12d: P2 M Formalism Basic Notions Examples  CD entry le sum 6938a3ded12d
-- statement:
--   The P2 M Formalism Basic Notions Examples  CD entry le sum 6938a3ded12d construction uses the P2 M Formalism Basic Notions Examples  CD entry le sum 6938a3ded12d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/ExistsOmegaLeb.lean#L177-L180
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/ExistsOmegaLeb.lean#L177-L180

import Definitions.Def_Formalism_LocalRingCardinality_DataCD
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Upqcpt
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_ExistsOmegaLeb
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Examples₂ Formalism.BasicNotions.Examples₂.CD
open MeasureTheory Filter Topology Set Matrix Formalism.UG.P
open scoped ENNReal NNReal
variable (P Q : ℕ)
local notation "J" => Formalism.UG.Jpq P Q

theorem P2M_Formalism_BasicNotions_Examples__CD_entry_le_sum_6938a3ded12d (X : MM P Q) (i j : Fin P ⊕ Fin Q) : ‖X i j‖ ≤ ∑ i, ∑ j, ‖X i j‖ := by sorry

alias «Formalism».«BasicNotions».«Examples₂».«CD».«entry_le_sum» := P2M_Formalism_BasicNotions_Examples__CD_entry_le_sum_6938a3ded12d
