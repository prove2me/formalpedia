-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_R_germ_mem_nonZeroDivisors
-- name    : ReciprocityTheory.AnForm.R.germ_mem_nonZeroDivisors
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T13:53:30.528788+00:00
-- url     : https://prove2.me/theorems/44a2cee5-5f7e-5965-9ace-10331bc4d677
-- title:
--   R: germ mem non Zero Divisors
-- statement:
--   The R construction uses the germ mem non Zero Divisors property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/WChartsA.lean#L69-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/WChartsA.lean#L69-L76

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

theorem ReciprocityTheory.AnForm.R.germ_mem_nonZeroDivisors {W : Scheme.{0}} {V : W.Opens} (hV : IsAffineOpen V) {a : Γ(W, V)}
    (ha : a ∈ nonZeroDivisors Γ(W, V)) (w : W) (hw : w ∈ V) :
    W.presheaf.germ V w hw a ∈ nonZeroDivisors (W.presheaf.stalk w) := by sorry
