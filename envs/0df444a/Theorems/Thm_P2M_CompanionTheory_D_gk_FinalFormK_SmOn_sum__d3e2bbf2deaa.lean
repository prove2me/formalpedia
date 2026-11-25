-- Prove2me | Theorems.Thm_P2M_CompanionTheory_D_gk_FinalFormK_SmOn_sum__d3e2bbf2deaa
-- name    : P2M_CompanionTheory_D_gk_FinalFormK_SmOn_sum__d3e2bbf2deaa
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T13:57:10.081103+00:00
-- url     : https://prove2.me/theorems/b9166485-13d2-4e37-9d6b-e4e69afc3c75
-- title:
--   P2 M Companion Theory D gk Final Form K Sm On sum  d3e2bbf2deaa: P2 M Companion Theory D gk Final Form K Sm On sum  d3e2bbf2deaa
-- statement:
--   The P2 M Companion Theory D gk Final Form K Sm On sum  d3e2bbf2deaa construction uses the P2 M Companion Theory D gk Final Form K Sm On sum  d3e2bbf2deaa property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/KFiniteAnalyticVectors/OrbitDerivatives/HasDerivAtMatrixExpZero.lean#L198-L200
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/KFiniteAnalyticVectors/OrbitDerivatives/HasDerivAtMatrixExpZero.lean#L198-L200

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

theorem P2M_CompanionTheory_D_gk_FinalFormK_SmOn_sum__d3e2bbf2deaa {E V ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup V] [NormedSpace ℝ V]
    {A : Set E} {f : ι → E → V} (s : Finset ι) (hf : ∀ i ∈ s, SmOn A (f i)) : SmOn A fun a => ∑ i ∈ s, f i a := by sorry

alias «CompanionTheory».«D».«gk».«FinalFormK».«SmOn».«sum'» := P2M_CompanionTheory_D_gk_FinalFormK_SmOn_sum__d3e2bbf2deaa
