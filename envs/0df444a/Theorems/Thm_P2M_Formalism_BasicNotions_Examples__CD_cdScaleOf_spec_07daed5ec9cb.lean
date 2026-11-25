-- Prove2me | Theorems.Thm_P2M_Formalism_BasicNotions_Examples__CD_cdScaleOf_spec_07daed5ec9cb
-- name    : P2M_Formalism_BasicNotions_Examples__CD_cdScaleOf_spec_07daed5ec9cb
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T16:27:44.82302+00:00
-- url     : https://prove2.me/theorems/5da3a7ca-cb04-4297-b238-9f42272e93c4
-- title:
--   P2 M Formalism Basic Notions Examples  CD cd Scale Of spec 07daed5ec9cb: P2 M Formalism Basic Notions Examples  CD cd Scale Of spec 07daed5ec9cb
-- statement:
--   The P2 M Formalism Basic Notions Examples  CD cd Scale Of spec 07daed5ec9cb construction uses the P2 M Formalism Basic Notions Examples  CD cd Scale Of spec 07daed5ec9cb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/SignSplitEquivInl.lean#L210-L235
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/SignSplitEquivInl.lean#L210-L235

import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_HaarDensityNeZero
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_FrobeniusBoundOfMulNearOne
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_SignSplitEquivInl
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
open MeasureTheory Matrix Formalism.REAL Formalism.UG.P Topology
open scoped ENNReal NNReal
variable (C : CDHaar)

theorem P2M_Formalism_BasicNotions_Examples__CD_cdScaleOf_spec_07daed5ec9cb {n P Q : ℕ} (ε : Fin n → Bool) (e : Fin P ⊕ Fin Q ≃ Fin n)
    (h1 : ∀ i, ε (e (Sum.inl i)) = true) (h2 : ∀ j, ε (e (Sum.inr j)) = false) :
    0 < cdScaleOf C n ε ∧ (C.cd P Q).map (phi ε e h1 h2) = cdScaleOf C n ε • muG ε := by sorry

alias «Formalism».«BasicNotions».«Examples₂».«CD».«cdScaleOf_spec» := P2M_Formalism_BasicNotions_Examples__CD_cdScaleOf_spec_07daed5ec9cb
