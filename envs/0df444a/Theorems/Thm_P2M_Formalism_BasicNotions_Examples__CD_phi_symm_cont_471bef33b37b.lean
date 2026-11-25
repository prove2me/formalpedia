-- Prove2me | Theorems.Thm_P2M_Formalism_BasicNotions_Examples__CD_phi_symm_cont_471bef33b37b
-- name    : P2M_Formalism_BasicNotions_Examples__CD_phi_symm_cont_471bef33b37b
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T16:28:18.928916+00:00
-- url     : https://prove2.me/theorems/9fe8d0a3-fd5a-4a93-bfeb-c6538578e952
-- title:
--   P2 M Formalism Basic Notions Examples  CD phi symm cont 471bef33b37b: P2 M Formalism Basic Notions Examples  CD phi symm cont 471bef33b37b
-- statement:
--   The P2 M Formalism Basic Notions Examples  CD phi symm cont 471bef33b37b construction uses the P2 M Formalism Basic Notions Examples  CD phi symm cont 471bef33b37b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/SignSplitEquivInl.lean#L72-L79
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/SignSplitEquivInl.lean#L72-L79

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
variable {n P Q : ℕ} (ε : Fin n → Bool) (e : Fin P ⊕ Fin Q ≃ Fin n)
  (h1 : ∀ i, ε (e (Sum.inl i)) = true) (h2 : ∀ j, ε (e (Sum.inr j)) = false)

theorem P2M_Formalism_BasicNotions_Examples__CD_phi_symm_cont_471bef33b37b : Continuous (phi ε e h1 h2).symm := by sorry

alias «Formalism».«BasicNotions».«Examples₂».«CD».«phi_symm_cont» := P2M_Formalism_BasicNotions_Examples__CD_phi_symm_cont_471bef33b37b
