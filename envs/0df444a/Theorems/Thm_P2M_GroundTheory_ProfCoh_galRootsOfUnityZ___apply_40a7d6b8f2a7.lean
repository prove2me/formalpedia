-- Prove2me | Theorems.Thm_P2M_GroundTheory_ProfCoh_galRootsOfUnityZ___apply_40a7d6b8f2a7
-- name    : P2M_GroundTheory_ProfCoh_galRootsOfUnityZ___apply_40a7d6b8f2a7
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T06:25:30.919299+00:00
-- url     : https://prove2.me/theorems/e645c6c3-489e-43cc-93f6-32144838f129
-- title:
--   P2 M Ground Theory Prof Coh gal Roots Of Unity Z   apply 40a7d6b8f2a7: P2 M Ground Theory Prof Coh gal Roots Of Unity Z   apply 40a7d6b8f2a7
-- statement:
--   The P2 M Ground Theory Prof Coh gal Roots Of Unity Z   apply 40a7d6b8f2a7 construction uses the P2 M Ground Theory Prof Coh gal Roots Of Unity Z   apply 40a7d6b8f2a7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/GaloisModules/CoeGalRootsOfUnityHomApply.lean#L134-L136
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/GaloisModules/CoeGalRootsOfUnityHomApply.lean#L134-L136

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

theorem P2M_GroundTheory_ProfCoh_galRootsOfUnityZ___apply_40a7d6b8f2a7 (n : ℕ) (σ : Gal(L/K)) (x : Additive (rootsOfUnity n L)) :
    (galRootsOfUnityZ K L n).ρ σ x = Additive.ofMul (galRootsOfUnityHom K L n σ x.toMul) := by sorry

alias «GroundTheory».«ProfCoh».«galRootsOfUnityZ_ρ_apply» := P2M_GroundTheory_ProfCoh_galRootsOfUnityZ___apply_40a7d6b8f2a7

attribute [defeq] P2M_GroundTheory_ProfCoh_galRootsOfUnityZ___apply_40a7d6b8f2a7
