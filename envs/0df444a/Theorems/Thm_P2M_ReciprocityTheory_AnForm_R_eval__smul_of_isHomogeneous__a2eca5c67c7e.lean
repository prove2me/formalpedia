-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_AnForm_R_eval__smul_of_isHomogeneous__a2eca5c67c7e
-- name    : P2M_ReciprocityTheory_AnForm_R_eval__smul_of_isHomogeneous__a2eca5c67c7e
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T13:44:59.362856+00:00
-- url     : https://prove2.me/theorems/2aac658c-5f12-428a-97dc-bb28678a0f01
-- title:
--   P2 M Reciprocity Theory An Form R eval  smul of is Homogeneous  a2eca5c67c7e: P2 M Reciprocity Theory An Form R eval  smul of is Homogeneous  a2eca5c67c7e
-- statement:
--   The P2 M Reciprocity Theory An Form R eval  smul of is Homogeneous  a2eca5c67c7e construction uses the P2 M Reciprocity Theory An Form R eval  smul of is Homogeneous  a2eca5c67c7e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/ProjHypA.lean#L101-L114
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/ProjHypA.lean#L101-L114

import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ProjDehom
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_LogResStC
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_FinTypeQE
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ProjHypA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.R
open MvPolynomial AlgebraicGeometry CategoryTheory
noncomputable section
variable {K : Type} [Fintype K] [Nonempty K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem P2M_ReciprocityTheory_AnForm_R_eval__smul_of_isHomogeneous__a2eca5c67c7e {σ R : Type} [Fintype σ] [CommRing R] (g : ℂ →+* R)
    {f : MvPolynomial σ ℂ} {d : ℕ} (hf : f.IsHomogeneous d) (t : R) (y : σ → R) :
    eval₂ g (fun i => t * y i) f = t ^ d * eval₂ g y f := by sorry

alias «ReciprocityTheory».«AnForm».«R».«eval₂_smul_of_isHomogeneous'» := P2M_ReciprocityTheory_AnForm_R_eval__smul_of_isHomogeneous__a2eca5c67c7e
