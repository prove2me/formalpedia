-- Prove2me | Theorems.Thm_P2M_Formalism_BasicNotions_Examples__CD_cdScaleOf_tie_64b2462b285c
-- name    : P2M_Formalism_BasicNotions_Examples__CD_cdScaleOf_tie_64b2462b285c
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T16:26:56.986005+00:00
-- url     : https://prove2.me/theorems/b25d8fce-64e7-573d-9348-b80080f77196
-- title:
--   P2 M Formalism Basic Notions Examples  CD cd Scale Of tie 64b2462b285c: P2 M Formalism Basic Notions Examples  CD cd Scale Of tie 64b2462b285c
-- statement:
--   The P2 M Formalism Basic Notions Examples  CD cd Scale Of tie 64b2462b285c construction uses the P2 M Formalism Basic Notions Examples  CD cd Scale Of tie 64b2462b285c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/SignSplitEquivInl.lean#L240-L248
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/SignSplitEquivInl.lean#L240-L248

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

theorem P2M_Formalism_BasicNotions_Examples__CD_cdScaleOf_tie_64b2462b285c (n : ℕ) (ε : Fin n → Bool) (P Q : ℕ) (e : Fin P ⊕ Fin Q ≃ Fin n)
    (h1 : ∀ i, ε (e (Sum.inl i)) = true) (h2 : ∀ j, ε (e (Sum.inr j)) = false)
    (A : Set (UJ ε)) (hA : MeasurableSet A) :
    ((cdScaleOf C n ε : ℝ≥0∞) • muG ε) A =
      C.cd P Q {g | ∃ a ∈ A, ((a : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) =
        Matrix.reindex e e (UpqT.mat g)} := by sorry

alias «Formalism».«BasicNotions».«Examples₂».«CD».«cdScaleOf_tie» := P2M_Formalism_BasicNotions_Examples__CD_cdScaleOf_tie_64b2462b285c
