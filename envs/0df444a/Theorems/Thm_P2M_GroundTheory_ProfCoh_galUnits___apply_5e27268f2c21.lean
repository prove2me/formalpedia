-- Prove2me | Theorems.Thm_P2M_GroundTheory_ProfCoh_galUnits___apply_5e27268f2c21
-- name    : P2M_GroundTheory_ProfCoh_galUnits___apply_5e27268f2c21
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T06:25:42.356907+00:00
-- url     : https://prove2.me/theorems/4abfe231-83bf-4264-b2b8-557983cb8dd0
-- title:
--   P2 M Ground Theory Prof Coh gal Units   apply 5e27268f2c21: P2 M Ground Theory Prof Coh gal Units   apply 5e27268f2c21
-- statement:
--   The P2 M Ground Theory Prof Coh gal Units   apply 5e27268f2c21 construction uses the P2 M Ground Theory Prof Coh gal Units   apply 5e27268f2c21 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/GaloisModules/CoeGalRootsOfUnityHomApply.lean#L119-L121
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/GaloisModules/CoeGalRootsOfUnityHomApply.lean#L119-L121

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

theorem P2M_GroundTheory_ProfCoh_galUnits___apply_5e27268f2c21 (σ : Gal(L/K)) (x : Additive Lˣ) :
    (galUnits.{w} K L).ρ σ x = Additive.ofMul (galUnitsHom K L σ x.toMul) := by sorry

alias «GroundTheory».«ProfCoh».«galUnits_ρ_apply» := P2M_GroundTheory_ProfCoh_galUnits___apply_5e27268f2c21

attribute [defeq] P2M_GroundTheory_ProfCoh_galUnits___apply_5e27268f2c21
