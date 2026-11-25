-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_R_isAffineOpen_of_iso
-- name    : ReciprocityTheory.AnForm.R.isAffineOpen_of_iso
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T14:07:14.645076+00:00
-- url     : https://prove2.me/theorems/a7549a5f-2d9a-416f-a6a1-3e71b8d681b8
-- title:
--   R: is Affine Open of iso
-- statement:
--   The R construction uses the is Affine Open of iso property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/WChartsA.lean#L18-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/WChartsA.lean#L18-L20

import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ProjBCompl
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_WChartsA
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

theorem ReciprocityTheory.AnForm.R.isAffineOpen_of_iso {W : Scheme.{0}} (V : W.Opens) {A : CommRingCat.{0}}
    (e : V.toScheme ≅ Spec A) : IsAffineOpen V := by sorry
