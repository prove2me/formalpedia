-- Prove2me | Theorems.Thm_P2M_GroundTheory_ProfCoh_galAddInt___apply_e3c2bd0048b0
-- name    : P2M_GroundTheory_ProfCoh_galAddInt___apply_e3c2bd0048b0
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T06:26:17.918538+00:00
-- url     : https://prove2.me/theorems/f9f8a336-22ef-4de9-a8b2-e0c90d2be918
-- title:
--   P2 M Ground Theory Prof Coh gal Add Int   apply e3c2bd0048b0: P2 M Ground Theory Prof Coh gal Add Int   apply e3c2bd0048b0
-- statement:
--   The P2 M Ground Theory Prof Coh gal Add Int   apply e3c2bd0048b0 construction uses the P2 M Ground Theory Prof Coh gal Add Int   apply e3c2bd0048b0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/GaloisModules/CoeGalRootsOfUnityHomApply.lean#L111-L112
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/GaloisModules/CoeGalRootsOfUnityHomApply.lean#L111-L112

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

theorem P2M_GroundTheory_ProfCoh_galAddInt___apply_e3c2bd0048b0 (σ : Gal(L/K)) (x : L) : (galAddInt.{w} K L).ρ σ x = σ x := by sorry

alias «GroundTheory».«ProfCoh».«galAddInt_ρ_apply» := P2M_GroundTheory_ProfCoh_galAddInt___apply_e3c2bd0048b0

attribute [defeq] P2M_GroundTheory_ProfCoh_galAddInt___apply_e3c2bd0048b0
