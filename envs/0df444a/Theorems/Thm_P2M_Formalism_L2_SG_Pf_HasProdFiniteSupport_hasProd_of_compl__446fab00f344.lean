-- Prove2me | Theorems.Thm_P2M_Formalism_L2_SG_Pf_HasProdFiniteSupport_hasProd_of_compl__446fab00f344
-- name    : P2M_Formalism_L2_SG_Pf_HasProdFiniteSupport_hasProd_of_compl__446fab00f344
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T07:54:18.535676+00:00
-- url     : https://prove2.me/theorems/217c2e68-fea9-56cc-aef8-9ddc368ed2f9
-- title:
--   P2 M Formalism L2 SG Pf Has Prod Finite Support has Prod of compl  446fab00f344: P2 M Formalism L2 SG Pf Has Prod Finite Support has Prod of compl  446fab00f344
-- statement:
--   The P2 M Formalism L2 SG Pf Has Prod Finite Support has Prod of compl  446fab00f344 construction uses the P2 M Formalism L2 SG Pf Has Prod Finite Support has Prod of compl  446fab00f344 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/DualFamilyCounting/HasProdFiniteSupport.lean#L56-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/DualFamilyCounting/HasProdFiniteSupport.lean#L56-L66

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

theorem P2M_Formalism_L2_SG_Pf_HasProdFiniteSupport_hasProd_of_compl__446fab00f344 (s : Finset ι) {f : ι → ℝ} {a : ℝ}
    (h : HasProd (fun i : {i // i ∉ s} => f i) a) : HasProd f (a * ∏ i : s, f i) := by sorry

alias «Formalism».«L2».«SG».«Pf».«HasProdFiniteSupport».«hasProd_of_compl'» := P2M_Formalism_L2_SG_Pf_HasProdFiniteSupport_hasProd_of_compl__446fab00f344
