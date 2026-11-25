-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_exists_perp_hermitian_reduction
-- name    : ReciprocityTheory.ChartRestriction.G.FD.exists_perp_hermitian_reduction
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T10:27:14.264459+00:00
-- url     : https://prove2.me/theorems/bd8f769d-a737-5101-97c2-a948924f65f8
-- title:
--   FD: exists perp hermitian reduction
-- statement:
--   The FD construction uses the exists perp hermitian reduction property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/ExistsPerpHermitianReduction.lean#L13-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/ExistsPerpHermitianReduction.lean#L13-L32

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_ExistsUnitaryBasisSameFlag
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_GramMatrixExistence
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_ExistsPerpHermitianReduction
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open NumberField Complex Matrix
open scoped ComplexConjugate
noncomputable section
variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]

theorem ReciprocityTheory.ChartRestriction.G.FD.exists_perp_hermitian_reduction (r : ℕ) (X : DataX E r) (ξ : Fin r → E) (z0 : Frame X.Ψ r)
    (f : X.Ψ → Fin (r - 2) → Fin r → ℂ) (hξ : X.IsIso ξ) (hz : z0 ∈ X.dom) (hf : X.UBasis z0 ξ f) :
    ∃ (β : Fin (r - 2) → Fin r → E) (S : ReciprocityTheory.MultiplicativeHeights.HermForm E (r - 2))
      (LB : Submodule (𝓞 E) (Fin (r - 2) → E)) (Q : X.Ψ → Matrix (Fin (r - 2)) (Fin (r - 2)) ℂ),
      (∀ k, herm X.Gm (β k) ξ = 0) ∧
      LinearIndependent E (Fin.cons ξ β : Fin (r - 2 + 1) → Fin r → E) ∧
      (∀ x : Fin r → E, herm X.Gm x ξ = 0 → ∃ (c : Fin (r - 2) → E) (e : E), x = ∑ k, c k • β k + e • ξ) ∧
      (∀ c c' : Fin (r - 2) → E, S.h c c' = herm X.Gm (∑ k, c' k • β k) (∑ k, c k • β k)) ∧
      (∀ c : Fin (r - 2) → E, c ∈ LB ↔ ∃ e : E, ∑ k, c k • β k + e • ξ ∈ X.L') ∧
      ReciprocityTheory.MultiplicativeHeights.IsLattice LB ∧ ReciprocityTheory.MultiplicativeHeights.IsSelfDual S LB ∧
      (∀ τ, (Q τ).det ≠ 0) ∧
      (∀ τ (c c' : Fin (r - 2) → E), τ.1 (S.h c c') =
        ReciprocityTheory.MultiplicativeHeights.jForm (X.p0 - 1) (Q τ *ᵥ ReciprocityTheory.MultiplicativeHeights.embVec τ.1 c) (Q τ *ᵥ ReciprocityTheory.MultiplicativeHeights.embVec τ.1 c')) ∧
      (∀ τ (c : Fin (r - 2) → E), X.ucomp z0 ξ (X.embV (∑ k, c k • β k)) τ =
        ∑ k, (Q τ *ᵥ ReciprocityTheory.MultiplicativeHeights.embVec τ.1 c) k • f τ k) := by sorry
