-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_GramDeterminantReal_pv_orth
-- name    : ReciprocityTheory.ChartRestriction.G.FD.GramDeterminantReal.pv_orth
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T05:27:53.361373+00:00
-- url     : https://prove2.me/theorems/976bc21c-294a-4b74-b3a0-b4b2797a25e1
-- title:
--   Gram Determinant Real: pv orth
-- statement:
--   The Gram Determinant Real construction uses the pv orth property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/GramDeterminantReal.lean#L44-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/GramDeterminantReal.lean#L44-L51

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_GramDeterminantReal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.GramDeterminantReal
open Complex Matrix
open scoped ComplexConjugate
noncomputable section
variable {E : Type} [Field E] {r : ℕ} (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E)
variable {n : ℕ} (f : Fin n → Fin r → ℂ) (e : Fin r → ℂ)

theorem ReciprocityTheory.ChartRestriction.G.FD.GramDeterminantReal.pv_orth (hA : IsUnit (gramF τ G f).det) (d : Fin n) :
    hermC τ G (pv τ G f e) (f d) = cv τ G f e d := by sorry
