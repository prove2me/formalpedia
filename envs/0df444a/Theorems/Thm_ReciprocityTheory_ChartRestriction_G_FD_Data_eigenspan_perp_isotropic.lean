-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_Data_eigenspan_perp_isotropic
-- name    : ReciprocityTheory.ChartRestriction.G.FD.Data.eigenspan_perp_isotropic
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T10:27:04.439737+00:00
-- url     : https://prove2.me/theorems/49029f86-9a73-5421-b53d-bfe2c6f97faa
-- title:
--   Data: eigenspan perp isotropic
-- statement:
--   The Data construction uses the eigenspan perp isotropic property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/OrthonormalShortVectorBoundOf.lean#L42-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/OrthonormalShortVectorBoundOf.lean#L42-L68

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_ReducedLatticeShortBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_GramSchmidtEigenframe
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_UnitaryFixingIsotropicPlane
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_UnitaryComplementMoveOfIsotropic
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FinrankEqTwoMulHalfDegree
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_OrthonormalShortVectorBoundOf
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
open ReciprocityTheory.ChartRestriction.G.FD.Data
variable {r : ℕ} (X : Data E r)

theorem ReciprocityTheory.ChartRestriction.G.FD.Data.eigenspan_perp_isotropic {z0 : Frame X.Ψ r} {ξ : Fin r → E} {f : X.Ψ → Fin (r - 2) → Fin r → ℂ}
    (hf : X.UBasis z0 ξ f) (τ : X.Ψ) (s : Set (Fin (r - 2))) (σ : ℂ)
    (hs : ∀ k ∈ s, (if (k : ℕ) < X.p0 - 1 then I else -I) = σ) (v : Fin r → ℂ)
    (hv : v ∈ Submodule.span ℂ (f τ '' s)) :
    hermC τ.1 X.Gm v (emb τ.1 ξ) = 0 ∧ hermC τ.1 X.Gm (X.Jt z0 τ v) (emb τ.1 ξ) = 0 ∧
      X.Jt z0 τ v = σ • v := by sorry
