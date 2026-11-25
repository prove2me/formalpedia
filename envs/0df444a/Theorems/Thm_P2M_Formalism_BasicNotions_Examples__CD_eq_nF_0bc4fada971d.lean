-- Prove2me | Theorems.Thm_P2M_Formalism_BasicNotions_Examples__CD_eq_nF_0bc4fada971d
-- name    : P2M_Formalism_BasicNotions_Examples__CD_eq_nF_0bc4fada971d
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T16:27:46.684268+00:00
-- url     : https://prove2.me/theorems/08fdcab1-218f-416b-82d2-f90724dd8356
-- title:
--   P2 M Formalism Basic Notions Examples  CD eq n F 0bc4fada971d: P2 M Formalism Basic Notions Examples  CD eq n F 0bc4fada971d
-- statement:
--   The P2 M Formalism Basic Notions Examples  CD eq n F 0bc4fada971d construction uses the P2 M Formalism Basic Notions Examples  CD eq n F 0bc4fada971d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/SignSplitEquivInl.lean#L176-L191
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/SignSplitEquivInl.lean#L176-L191

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

theorem P2M_Formalism_BasicNotions_Examples__CD_eq_nF_0bc4fada971d {n P Q : ℕ} (ε : Fin n → Bool) (e : Fin P ⊕ Fin Q ≃ Fin n)
    (h1 : ∀ i, ε (e (Sum.inl i)) = true) (h2 : ∀ j, ε (e (Sum.inr j)) = false) : Q = nF ε := by sorry

alias «Formalism».«BasicNotions».«Examples₂».«CD».«eq_nF» := P2M_Formalism_BasicNotions_Examples__CD_eq_nF_0bc4fada971d
