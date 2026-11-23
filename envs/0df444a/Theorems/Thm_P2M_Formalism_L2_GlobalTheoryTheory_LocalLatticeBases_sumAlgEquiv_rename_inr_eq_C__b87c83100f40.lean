-- Prove2me | Theorems.Thm_P2M_Formalism_L2_GlobalTheoryTheory_LocalLatticeBases_sumAlgEquiv_rename_inr_eq_C__b87c83100f40
-- name    : P2M_Formalism_L2_GlobalTheoryTheory_LocalLatticeBases_sumAlgEquiv_rename_inr_eq_C__b87c83100f40
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:05:42.058839+00:00
-- url     : https://prove2.me/theorems/7c32ccd1-00e3-49e2-ab03-97da266c7c03
-- title:
--   P2 M Formalism L2 Global Theory Theory Local Lattice Bases sum Alg Equiv rename inr eq C  b87c83100f40: P2 M Formalism L2 Global Theory Theory Local Lattice Bases sum Alg Equiv rename inr eq C  b87c83
-- statement:
--   The P2 M Formalism L2 Global Theory Theory Local Lattice Bases sum Alg Equiv rename inr eq C  b87c83100f40 construction uses the P2 M Formalism L2 Global Theory Theory Local Lattice Bases sum Alg Equiv rename inr eq C  b87c83100f40 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GlobalTheory/GL6/LinearIndependentProdRenameOfCard.lean#L16-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GlobalTheory/GL6/LinearIndependentProdRenameOfCard.lean#L16-L19

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_GL6_LinearIndependentProdRenameOfCard
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory.LocalLatticeBases
open MvPolynomial
variable {K : Type*} [Field K] {S₁ S₂ : Type*}

theorem P2M_Formalism_L2_GlobalTheoryTheory_LocalLatticeBases_sumAlgEquiv_rename_inr_eq_C__b87c83100f40 (b : MvPolynomial S₂ K) :
    sumAlgEquiv K S₁ S₂ (rename Sum.inr b) = C b := by sorry

alias «Formalism».«L2».«GlobalTheoryTheory».«LocalLatticeBases».«sumAlgEquiv_rename_inr_eq_C'» := P2M_Formalism_L2_GlobalTheoryTheory_LocalLatticeBases_sumAlgEquiv_rename_inr_eq_C__b87c83100f40
