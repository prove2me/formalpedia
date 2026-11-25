-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_EigenframeMatrices_Mmat_unitary
-- name    : ReciprocityTheory.ChartRestriction.G.FD.EigenframeMatrices.Mmat_unitary
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T10:13:58.56221+00:00
-- url     : https://prove2.me/theorems/a00b6a97-2831-446f-90a0-97a5aefc0758
-- title:
--   Eigenframe Matrices: Mmat unitary
-- statement:
--   The Eigenframe Matrices construction uses the Mmat unitary property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/MmatUnitary.lean#L113-L143
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/MmatUnitary.lean#L113-L143

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
variable (hG : ∀ a b, cc (G a b) = G b a)
  (hf : ∀ k l, hermC τ G (f k) (f l) = if k = l then (if (k : ℕ) < p then 1 else -1) else 0)
include hG hf

theorem ReciprocityTheory.ChartRestriction.G.FD.EigenframeMatrices.Mmat_unitary (hgf : ∀ k, g k ∈ Submodule.span ℂ (Set.range f))
    (hg : ∀ k l, hermC τ G (g k) (g l) = if k = l then (if (k : ℕ) < p then 1 else -1) else 0)
    (v w : Fin r → ℂ) :
    hermC τ G (Mmat τ G p f g *ᵥ v) (Mmat τ G p f g *ᵥ w) = hermC τ G v w := by sorry
