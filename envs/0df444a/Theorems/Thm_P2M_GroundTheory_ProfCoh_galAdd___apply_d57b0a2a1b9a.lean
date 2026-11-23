-- Prove2me | Theorems.Thm_P2M_GroundTheory_ProfCoh_galAdd___apply_d57b0a2a1b9a
-- name    : P2M_GroundTheory_ProfCoh_galAdd___apply_d57b0a2a1b9a
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T06:26:22.215878+00:00
-- url     : https://prove2.me/theorems/fbd723ac-2f86-4cd3-a83b-13b9fd0649fe
-- title:
--   P2 M Ground Theory Prof Coh gal Add   apply d57b0a2a1b9a: P2 M Ground Theory Prof Coh gal Add   apply d57b0a2a1b9a
-- statement:
--   The P2 M Ground Theory Prof Coh gal Add   apply d57b0a2a1b9a construction uses the P2 M Ground Theory Prof Coh gal Add   apply d57b0a2a1b9a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/GaloisModules/CoeGalRootsOfUnityHomApply.lean#L107-L108
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/GaloisModules/CoeGalRootsOfUnityHomApply.lean#L107-L108

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_GaloisModules_CoeGalRootsOfUnityHomApply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.ProfCoh
universe w u v
variable (K : Type*) (L : Type u) [Field K] [Field L] [Algebra K L]
variable {K L}

theorem P2M_GroundTheory_ProfCoh_galAdd___apply_d57b0a2a1b9a (σ : Gal(L/K)) (x : L) : (galAdd K L).ρ σ x = σ x := by sorry

alias «GroundTheory».«ProfCoh».«galAdd_ρ_apply» := P2M_GroundTheory_ProfCoh_galAdd___apply_d57b0a2a1b9a

attribute [defeq] P2M_GroundTheory_ProfCoh_galAdd___apply_d57b0a2a1b9a
