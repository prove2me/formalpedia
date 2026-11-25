-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_AnForm_R_exists_eval__chartCoord_95f51dd56702
-- name    : P2M_ReciprocityTheory_AnForm_R_exists_eval__chartCoord_95f51dd56702
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T14:02:53.776546+00:00
-- url     : https://prove2.me/theorems/0bb9da8d-fd58-4b39-94fc-8cae5b164ba7
-- title:
--   P2 M Reciprocity Theory An Form R exists eval  chart Coord 95f51dd56702: P2 M Reciprocity Theory An Form R exists eval  chart Coord 95f51dd56702
-- statement:
--   The P2 M Reciprocity Theory An Form R exists eval  chart Coord 95f51dd56702 construction uses the P2 M Reciprocity Theory An Form R exists eval  chart Coord 95f51dd56702 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/WChartsD.lean#L76-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/WChartsD.lean#L76-L81

import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_WChartsA
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_WChartsD
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

theorem P2M_ReciprocityTheory_AnForm_R_exists_eval__chartCoord_95f51dd56702 {P : Ideal (MvPolynomial (Σ k, ι k) ℂ)} (hP : IsMultiHomogIdeal P)
    (p : (k : K) → ι k) (r : Γ(projX P hP, (chartOpen hP p).1)) :
    ∃ f : MvPolynomial (Σ k, ι k) ℂ, r = eval₂ (constSec (toSpecC hP) (chartOpen hP p).1) (chartCoord hP p) f := by sorry

alias «ReciprocityTheory».«AnForm».«R».«exists_eval₂_chartCoord» := P2M_ReciprocityTheory_AnForm_R_exists_eval__chartCoord_95f51dd56702
