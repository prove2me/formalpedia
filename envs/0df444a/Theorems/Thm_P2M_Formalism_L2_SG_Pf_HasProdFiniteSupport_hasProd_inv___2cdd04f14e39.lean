-- Prove2me | Theorems.Thm_P2M_Formalism_L2_SG_Pf_HasProdFiniteSupport_hasProd_inv___2cdd04f14e39
-- name    : P2M_Formalism_L2_SG_Pf_HasProdFiniteSupport_hasProd_inv___2cdd04f14e39
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T07:04:43.953753+00:00
-- url     : https://prove2.me/theorems/5c230c8d-8882-58c8-9a39-83131d9df707
-- title:
--   P2 M Formalism L2 SG Pf Has Prod Finite Support has Prod inv   2cdd04f14e39: P2 M Formalism L2 SG Pf Has Prod Finite Support has Prod inv   2cdd04f14e39
-- statement:
--   The P2 M Formalism L2 SG Pf Has Prod Finite Support has Prod inv   2cdd04f14e39 construction uses the P2 M Formalism L2 SG Pf Has Prod Finite Support has Prod inv   2cdd04f14e39 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/DualFamilyCounting/HasProdFiniteSupport.lean#L11-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/DualFamilyCounting/HasProdFiniteSupport.lean#L11-L15

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_HasProdFiniteSupport
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.HasProdFiniteSupport
open Filter Topology
variable {ι : Type*}

theorem P2M_Formalism_L2_SG_Pf_HasProdFiniteSupport_hasProd_inv___2cdd04f14e39 {f : ι → ℝ} {a : ℝ} (h : HasProd f a) (ha : a ≠ 0) :
    HasProd (fun i => (f i)⁻¹) a⁻¹ := by sorry

alias «Formalism».«L2».«SG».«Pf».«HasProdFiniteSupport».«hasProd_inv₀'» := P2M_Formalism_L2_SG_Pf_HasProdFiniteSupport_hasProd_inv___2cdd04f14e39
