-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_EigenframeMatrices_Mmat_mulVec
-- name    : ReciprocityTheory.ChartRestriction.G.FD.EigenframeMatrices.Mmat_mulVec
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:45:30.734585+00:00
-- url     : https://prove2.me/theorems/8f5b7a55-f70b-4636-ba57-f018f6224dcb
-- title:
--   Eigenframe Matrices: Mmat mul Vec
-- statement:
--   The Eigenframe Matrices construction uses the Mmat mul Vec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/MmatUnitary.lean#L23-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/MmatUnitary.lean#L23-L33

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_PerpSpanRight
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_MmatUnitary
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.EigenframeMatrices
open NumberField Complex Matrix ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.GramSchmidtSelfImaginary
open scoped ComplexConjugate
noncomputable section
variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E] {r : ℕ}
  (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) {n : ℕ} (p : ℕ) (f g : Fin n → Fin r → ℂ)

theorem ReciprocityTheory.ChartRestriction.G.FD.EigenframeMatrices.Mmat_mulVec (v : Fin r → ℂ) :
    Mmat τ G p f g *ᵥ v = v + ∑ k, (eps p k * hermC τ G v (f k)) • (g k - f k) := by sorry
