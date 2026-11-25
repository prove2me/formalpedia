-- Prove2me | Theorems.Thm_P2M_Formalism_BasicNotions_Examples__CD_eq_nT_b82156c5084c
-- name    : P2M_Formalism_BasicNotions_Examples__CD_eq_nT_b82156c5084c
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T16:27:03.853631+00:00
-- url     : https://prove2.me/theorems/4545162f-6789-5298-a17d-81e362d39ea5
-- title:
--   P2 M Formalism Basic Notions Examples  CD eq n T b82156c5084c: P2 M Formalism Basic Notions Examples  CD eq n T b82156c5084c
-- statement:
--   The P2 M Formalism Basic Notions Examples  CD eq n T b82156c5084c construction uses the P2 M Formalism Basic Notions Examples  CD eq n T b82156c5084c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/SignSplitEquivInl.lean#L159-L174
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/SignSplitEquivInl.lean#L159-L174

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

theorem P2M_Formalism_BasicNotions_Examples__CD_eq_nT_b82156c5084c {n P Q : ℕ} (ε : Fin n → Bool) (e : Fin P ⊕ Fin Q ≃ Fin n)
    (h1 : ∀ i, ε (e (Sum.inl i)) = true) (h2 : ∀ j, ε (e (Sum.inr j)) = false) : P = nT ε := by sorry

alias «Formalism».«BasicNotions».«Examples₂».«CD».«eq_nT» := P2M_Formalism_BasicNotions_Examples__CD_eq_nT_b82156c5084c
