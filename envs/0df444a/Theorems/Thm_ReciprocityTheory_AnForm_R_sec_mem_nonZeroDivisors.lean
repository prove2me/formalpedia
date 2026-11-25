-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_R_sec_mem_nonZeroDivisors
-- name    : ReciprocityTheory.AnForm.R.sec_mem_nonZeroDivisors
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T13:53:23.991799+00:00
-- url     : https://prove2.me/theorems/5ca4de51-2e34-513a-9905-8f28cafc935d
-- title:
--   R: sec mem non Zero Divisors
-- statement:
--   The R construction uses the sec mem non Zero Divisors property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/WChartsA.lean#L22-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/WChartsA.lean#L22-L31

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

theorem ReciprocityTheory.AnForm.R.sec_mem_nonZeroDivisors {W : Scheme.{0}} (V : W.Opens) {A : CommRingCat.{0}}
    (e : V.toScheme ≅ Spec A) {a : A} (ha : a ∈ nonZeroDivisors A) :
    V.topIso.hom (e.hom.appTop ((Scheme.ΓSpecIso A).inv a)) ∈ nonZeroDivisors Γ(W, V) := by sorry
