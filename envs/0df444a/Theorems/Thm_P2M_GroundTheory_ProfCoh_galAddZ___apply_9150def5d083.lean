-- Prove2me | Theorems.Thm_P2M_GroundTheory_ProfCoh_galAddZ___apply_9150def5d083
-- name    : P2M_GroundTheory_ProfCoh_galAddZ___apply_9150def5d083
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T06:26:12.756282+00:00
-- url     : https://prove2.me/theorems/9383e343-cce7-44c8-b209-3d3a8b908e31
-- title:
--   P2 M Ground Theory Prof Coh gal Add Z   apply 9150def5d083: P2 M Ground Theory Prof Coh gal Add Z   apply 9150def5d083
-- statement:
--   The P2 M Ground Theory Prof Coh gal Add Z   apply 9150def5d083 construction uses the P2 M Ground Theory Prof Coh gal Add Z   apply 9150def5d083 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/GaloisModules/CoeGalRootsOfUnityHomApply.lean#L115-L116
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/GaloisModules/CoeGalRootsOfUnityHomApply.lean#L115-L116

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

theorem P2M_GroundTheory_ProfCoh_galAddZ___apply_9150def5d083 (σ : Gal(L/K)) (x : L) : (galAddZ K L).ρ σ x = σ x := by sorry

alias «GroundTheory».«ProfCoh».«galAddZ_ρ_apply» := P2M_GroundTheory_ProfCoh_galAddZ___apply_9150def5d083

attribute [defeq] P2M_GroundTheory_ProfCoh_galAddZ___apply_9150def5d083
