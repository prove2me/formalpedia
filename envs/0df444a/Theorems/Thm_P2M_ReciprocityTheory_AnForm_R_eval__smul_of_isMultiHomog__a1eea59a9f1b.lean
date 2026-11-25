-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_AnForm_R_eval__smul_of_isMultiHomog__a1eea59a9f1b
-- name    : P2M_ReciprocityTheory_AnForm_R_eval__smul_of_isMultiHomog__a1eea59a9f1b
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T13:08:27.672229+00:00
-- url     : https://prove2.me/theorems/70a4d191-5165-5246-8c0a-5a1c9bdf07a9
-- title:
--   P2 M Reciprocity Theory An Form R eval  smul of is Multi Homog  a1eea59a9f1b: P2 M Reciprocity Theory An Form R eval  smul of is Multi Homog  a1eea59a9f1b
-- statement:
--   The P2 M Reciprocity Theory An Form R eval  smul of is Multi Homog  a1eea59a9f1b construction uses the P2 M Reciprocity Theory An Form R eval  smul of is Multi Homog  a1eea59a9f1b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/ProjHypA.lean#L84-L99
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/ProjHypA.lean#L84-L99

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

theorem P2M_ReciprocityTheory_AnForm_R_eval__smul_of_isMultiHomog__a1eea59a9f1b {R : Type} [CommRing R] (g : ℂ →+* R)
    {f : MvPolynomial (Σ k, ι k) ℂ} {a : K → ℕ} (hf : IsMultiHomog f a) (c : K → R)
    (y : (Σ k, ι k) → R) :
    eval₂ g (fun q => c q.1 * y q) f = (∏ k, c k ^ a k) * eval₂ g y f := by sorry

alias «ReciprocityTheory».«AnForm».«R».«eval₂_smul_of_isMultiHomog'» := P2M_ReciprocityTheory_AnForm_R_eval__smul_of_isMultiHomog__a1eea59a9f1b
