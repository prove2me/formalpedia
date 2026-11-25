-- Prove2me | Theorems.Thm_P2M_Formalism_L2_SG_Pf_HasProdFiniteSupport_hasProd_compl_of__0104220ab595
-- name    : P2M_Formalism_L2_SG_Pf_HasProdFiniteSupport_hasProd_compl_of__0104220ab595
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T07:55:26.744093+00:00
-- url     : https://prove2.me/theorems/59375d74-8acf-47c6-9187-b9c108556202
-- title:
--   P2 M Formalism L2 SG Pf Has Prod Finite Support has Prod compl of  0104220ab595: P2 M Formalism L2 SG Pf Has Prod Finite Support has Prod compl of  0104220ab595
-- statement:
--   The P2 M Formalism L2 SG Pf Has Prod Finite Support has Prod compl of  0104220ab595 construction uses the P2 M Formalism L2 SG Pf Has Prod Finite Support has Prod compl of  0104220ab595 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/DualFamilyCounting/HasProdFiniteSupport.lean#L68-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/DualFamilyCounting/HasProdFiniteSupport.lean#L68-L82

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

theorem P2M_Formalism_L2_SG_Pf_HasProdFiniteSupport_hasProd_compl_of__0104220ab595 (s : Finset ι) {f : ι → ℝ} {a : ℝ} (h : HasProd f a) (hf : ∀ i ∈ s, f i ≠ 0) :
    HasProd (fun i : {i // i ∉ s} => f i) (a * (∏ i : s, f i)⁻¹) := by sorry

alias «Formalism».«L2».«SG».«Pf».«HasProdFiniteSupport».«hasProd_compl_of'» := P2M_Formalism_L2_SG_Pf_HasProdFiniteSupport_hasProd_compl_of__0104220ab595
