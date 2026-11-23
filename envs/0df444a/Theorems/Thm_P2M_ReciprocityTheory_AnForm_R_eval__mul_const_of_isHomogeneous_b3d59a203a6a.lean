-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_AnForm_R_eval__mul_const_of_isHomogeneous_b3d59a203a6a
-- name    : P2M_ReciprocityTheory_AnForm_R_eval__mul_const_of_isHomogeneous_b3d59a203a6a
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:03:47.460376+00:00
-- url     : https://prove2.me/theorems/5786755f-017e-484b-a215-6afd9712e06f
-- title:
--   P2 M Reciprocity Theory An Form R eval  mul const of is Homogeneous b3d59a203a6a: P2 M Reciprocity Theory An Form R eval  mul const of is Homogeneous b3d59a203a6a
-- statement:
--   The P2 M Reciprocity Theory An Form R eval  mul const of is Homogeneous b3d59a203a6a construction uses the P2 M Reciprocity Theory An Form R eval  mul const of is Homogeneous b3d59a203a6a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/ProjDehomA.lean#L9-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/ProjDehomA.lean#L9-L19

import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_SegreIdealIsHomogeneous
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ProjDehomA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.R
open MvPolynomial
noncomputable section

theorem P2M_ReciprocityTheory_AnForm_R_eval__mul_const_of_isHomogeneous_b3d59a203a6a {σ R S : Type*} [CommSemiring R] [CommSemiring S]
    (g : R →+* S) (y : σ → S) (t : S) {f : MvPolynomial σ R} {n : ℕ} (hf : f.IsHomogeneous n) :
    eval₂ g (fun i => y i * t) f = eval₂ g y f * t ^ n := by sorry

alias «ReciprocityTheory».«AnForm».«R».«eval₂_mul_const_of_isHomogeneous» := P2M_ReciprocityTheory_AnForm_R_eval__mul_const_of_isHomogeneous_b3d59a203a6a
