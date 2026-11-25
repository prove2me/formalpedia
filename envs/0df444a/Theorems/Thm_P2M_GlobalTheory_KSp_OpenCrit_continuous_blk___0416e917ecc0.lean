-- Prove2me | Theorems.Thm_P2M_GlobalTheory_KSp_OpenCrit_continuous_blk___0416e917ecc0
-- name    : P2M_GlobalTheory_KSp_OpenCrit_continuous_blk___0416e917ecc0
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T00:07:21.383189+00:00
-- url     : https://prove2.me/theorems/bee11700-d308-4f2f-9d2e-cee8821f9698
-- title:
--   P2 M Global Theory KSp Open Crit continuous blk   0416e917ecc0: P2 M Global Theory KSp Open Crit continuous blk   0416e917ecc0
-- statement:
--   The P2 M Global Theory KSp Open Crit continuous blk   0416e917ecc0 construction uses the P2 M Global Theory KSp Open Crit continuous blk   0416e917ecc0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsOpenSubgroupOfSiegelAndOppositeNhds.lean#L90-L91
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsOpenSubgroupOfSiegelAndOppositeNhds.lean#L90-L91

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_UnipVal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_QuadExtTopologyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsOpenSubgroupOfSiegelAndOppositeNhds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary Filter Topology
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)
noncomputable section
open GlobalTheory GlobalTheory.KSp GlobalTheory.KSp.OpenCrit
variable {F : Type} [Field F] {E : Type} [Field E] [Algebra F E] (c : E →ₐ[F] E)
  {ν : Type} [Fintype ν] [DecidableEq ν]
variable [TopologicalSpace E] [IsTopologicalRing E] [ContinuousInv₀ E] [T2Space E]

theorem P2M_GlobalTheory_KSp_OpenCrit_continuous_blk___0416e917ecc0 : Continuous fun g : UG c (stdJ ν E) => (mat c g).toBlocks₂₁ := by sorry

alias «GlobalTheory».«KSp».«OpenCrit».«continuous_blk₂₁» := P2M_GlobalTheory_KSp_OpenCrit_continuous_blk___0416e917ecc0
