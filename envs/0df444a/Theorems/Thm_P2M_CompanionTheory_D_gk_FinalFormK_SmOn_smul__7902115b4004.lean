-- Prove2me | Theorems.Thm_P2M_CompanionTheory_D_gk_FinalFormK_SmOn_smul__7902115b4004
-- name    : P2M_CompanionTheory_D_gk_FinalFormK_SmOn_smul__7902115b4004
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T23:52:23.908437+00:00
-- url     : https://prove2.me/theorems/c0862638-c0b3-4382-9865-d8b1f9a27432
-- title:
--   P2 M Companion Theory D gk Final Form K Sm On smul  7902115b4004: P2 M Companion Theory D gk Final Form K Sm On smul  7902115b4004
-- statement:
--   The P2 M Companion Theory D gk Final Form K Sm On smul  7902115b4004 construction uses the P2 M Companion Theory D gk Final Form K Sm On smul  7902115b4004 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/KFiniteAnalyticVectors/OrbitDerivatives/HasDerivAtMatrixExpZero.lean#L190-L196
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/KFiniteAnalyticVectors/OrbitDerivatives/HasDerivAtMatrixExpZero.lean#L190-L196

import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_HaarBumpFunctions_ExistsIsBump
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_SmoothOnAdditive
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_OrbitDerivatives_HasDerivAtMatrixExpZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology Set
open scoped ContDiff InnerProductSpace
noncomputable section
open CompanionTheory CompanionTheory.D CompanionTheory.D.gk CompanionTheory.D.gk.FinalFormK
open PI CompanionTheory.D.Upq.ModEx CompanionTheory.D.Upq.Sm CompanionTheory.D.gk.Poul
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ} {G : Set (Mat n)} {H H' : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] {σ : Mat n → (H →L[ℂ] H)} {τ : Mat n → (H' →L[ℂ] H')}
variable {L : Mat n → Prop}

theorem P2M_CompanionTheory_D_gk_FinalFormK_SmOn_smul__7902115b4004 {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup V] [NormedSpace ℂ V]
    {A : Set E} {c : E → ℂ} {f : E → V} (hc : SmOn A c) (hf : SmOn A f) : SmOn A fun a => c a • f a := by sorry

alias «CompanionTheory».«D».«gk».«FinalFormK».«SmOn».«smul'» := P2M_CompanionTheory_D_gk_FinalFormK_SmOn_smul__7902115b4004
