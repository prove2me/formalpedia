-- Prove2me | Theorems.Thm_P2M_GroundTheory_ProfCoh_galRootsOfUnity___apply_600492b04171
-- name    : P2M_GroundTheory_ProfCoh_galRootsOfUnity___apply_600492b04171
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T06:25:23.930589+00:00
-- url     : https://prove2.me/theorems/83bc8723-d711-4c66-8f74-e1e77a88a7aa
-- title:
--   P2 M Ground Theory Prof Coh gal Roots Of Unity   apply 600492b04171: P2 M Ground Theory Prof Coh gal Roots Of Unity   apply 600492b04171
-- statement:
--   The P2 M Ground Theory Prof Coh gal Roots Of Unity   apply 600492b04171 construction uses the P2 M Ground Theory Prof Coh gal Roots Of Unity   apply 600492b04171 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/GaloisModules/CoeGalRootsOfUnityHomApply.lean#L129-L131
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/GaloisModules/CoeGalRootsOfUnityHomApply.lean#L129-L131

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

theorem P2M_GroundTheory_ProfCoh_galRootsOfUnity___apply_600492b04171 (n : ℕ) (σ : Gal(L/K)) (x : Additive (rootsOfUnity n L)) :
    (galRootsOfUnity.{w} K L n).ρ σ x = Additive.ofMul (galRootsOfUnityHom K L n σ x.toMul) := by sorry

alias «GroundTheory».«ProfCoh».«galRootsOfUnity_ρ_apply» := P2M_GroundTheory_ProfCoh_galRootsOfUnity___apply_600492b04171

attribute [defeq] P2M_GroundTheory_ProfCoh_galRootsOfUnity___apply_600492b04171
