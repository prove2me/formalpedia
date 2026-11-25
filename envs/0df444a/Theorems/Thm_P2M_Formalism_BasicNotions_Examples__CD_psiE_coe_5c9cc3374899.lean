-- Prove2me | Theorems.Thm_P2M_Formalism_BasicNotions_Examples__CD_psiE_coe_5c9cc3374899
-- name    : P2M_Formalism_BasicNotions_Examples__CD_psiE_coe_5c9cc3374899
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T23:52:46.149434+00:00
-- url     : https://prove2.me/theorems/99740740-0c07-423e-a8ff-8f816f2b0ed0
-- title:
--   P2 M Formalism Basic Notions Examples  CD psi E coe 5c9cc3374899: P2 M Formalism Basic Notions Examples  CD psi E coe 5c9cc3374899
-- statement:
--   The P2 M Formalism Basic Notions Examples  CD psi E coe 5c9cc3374899 construction uses the P2 M Formalism Basic Notions Examples  CD psi E coe 5c9cc3374899 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/ExistsOmegaLeb.lean#L140-L143
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/ExistsOmegaLeb.lean#L140-L143

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

theorem P2M_Formalism_BasicNotions_Examples__CD_psiE_coe_5c9cc3374899 : ⇑(psiE P Q) = fun ab : lieU P Q × lieU P Q =>
    entries ((ab.1 : MM P Q) + Complex.I • (ab.2 : MM P Q)) := by sorry

alias «Formalism».«BasicNotions».«Examples₂».«CD».«psiE_coe» := P2M_Formalism_BasicNotions_Examples__CD_psiE_coe_5c9cc3374899
