-- Prove2me | Theorems.Thm_P2M_Formalism_L2_SG_Pf_HasProdFiniteSupport_hasProd_rpow__b4744c29bd11
-- name    : P2M_Formalism_L2_SG_Pf_HasProdFiniteSupport_hasProd_rpow__b4744c29bd11
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T07:54:33.134861+00:00
-- url     : https://prove2.me/theorems/efe1a8c6-f1e8-4320-94e2-50693e33f21c
-- title:
--   P2 M Formalism L2 SG Pf Has Prod Finite Support has Prod rpow  b4744c29bd11: P2 M Formalism L2 SG Pf Has Prod Finite Support has Prod rpow  b4744c29bd11
-- statement:
--   The P2 M Formalism L2 SG Pf Has Prod Finite Support has Prod rpow  b4744c29bd11 construction uses the P2 M Formalism L2 SG Pf Has Prod Finite Support has Prod rpow  b4744c29bd11 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/DualFamilyCounting/HasProdFiniteSupport.lean#L17-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/DualFamilyCounting/HasProdFiniteSupport.lean#L17-L21

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

theorem P2M_Formalism_L2_SG_Pf_HasProdFiniteSupport_hasProd_rpow__b4744c29bd11 {f : ι → ℝ} {a : ℝ} (p : ℝ) (hf : ∀ i, 0 ≤ f i) (h : HasProd f a) (ha : a ≠ 0) :
    HasProd (fun i => f i ^ p) (a ^ p) := by sorry

alias «Formalism».«L2».«SG».«Pf».«HasProdFiniteSupport».«hasProd_rpow'» := P2M_Formalism_L2_SG_Pf_HasProdFiniteSupport_hasProd_rpow__b4744c29bd11
