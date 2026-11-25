-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_AnForm_R_exists_closedPoint_stalk__4f0449e3f5d9
-- name    : P2M_ReciprocityTheory_AnForm_R_exists_closedPoint_stalk__4f0449e3f5d9
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T13:11:21.555347+00:00
-- url     : https://prove2.me/theorems/bcef8041-99cb-4204-bf7b-9b6fb45335e6
-- title:
--   P2 M Reciprocity Theory An Form R exists closed Point stalk  4f0449e3f5d9: P2 M Reciprocity Theory An Form R exists closed Point stalk  4f0449e3f5d9
-- statement:
--   The P2 M Reciprocity Theory An Form R exists closed Point stalk  4f0449e3f5d9 construction uses the P2 M Reciprocity Theory An Form R exists closed Point stalk  4f0449e3f5d9 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/ProjHypStalk.lean#L78-L134
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/ProjHypStalk.lean#L78-L134

import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ProjDehom
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_FromSpecResidueFieldAppTopIso
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_StalkLoc
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ProjHypStalk
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

theorem P2M_ReciprocityTheory_AnForm_R_exists_closedPoint_stalk__4f0449e3f5d9 {P : Ideal (MvPolynomial (Σ k, ι k) ℂ)} (hP : IsMultiHomogIdeal P)
    (p : (k : K) → ι k) (x : projX P hP) (hx : x ∈ (chartOpen hP p).1)
    (hc : IsClosed ({x} : Set (projX P hP))) :
    ∃ y : (Σ k, ι k) → ℂ, (∀ h ∈ chartIdeal P p, eval y h = 0) ∧
      (∀ q, val (toSpecC hP) (chartCoord hP p q) x hx = y q) ∧
      Nonempty ((projX P hP).presheaf.stalk x ≃+* locQ (chartIdeal P p) y) := by sorry

alias «ReciprocityTheory».«AnForm».«R».«exists_closedPoint_stalk'» := P2M_ReciprocityTheory_AnForm_R_exists_closedPoint_stalk__4f0449e3f5d9
