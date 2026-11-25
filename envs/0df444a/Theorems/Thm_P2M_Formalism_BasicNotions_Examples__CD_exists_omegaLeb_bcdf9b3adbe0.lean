-- Prove2me | Theorems.Thm_P2M_Formalism_BasicNotions_Examples__CD_exists_omegaLeb_bcdf9b3adbe0
-- name    : P2M_Formalism_BasicNotions_Examples__CD_exists_omegaLeb_bcdf9b3adbe0
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T23:52:50.381804+00:00
-- url     : https://prove2.me/theorems/76f6259c-a31f-4b4f-910d-7a718d60dd34
-- title:
--   P2 M Formalism Basic Notions Examples  CD exists omega Leb bcdf9b3adbe0: P2 M Formalism Basic Notions Examples  CD exists omega Leb bcdf9b3adbe0
-- statement:
--   The P2 M Formalism Basic Notions Examples  CD exists omega Leb bcdf9b3adbe0 construction uses the P2 M Formalism Basic Notions Examples  CD exists omega Leb bcdf9b3adbe0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/ExistsOmegaLeb.lean#L145-L165
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/ExistsOmegaLeb.lean#L145-L165

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

theorem P2M_Formalism_BasicNotions_Examples__CD_exists_omegaLeb_bcdf9b3adbe0 : ∃ lam : Measure (lieU P Q), IsOmegaLeb lam := by sorry

alias «Formalism».«BasicNotions».«Examples₂».«CD».«exists_omegaLeb» := P2M_Formalism_BasicNotions_Examples__CD_exists_omegaLeb_bcdf9b3adbe0
