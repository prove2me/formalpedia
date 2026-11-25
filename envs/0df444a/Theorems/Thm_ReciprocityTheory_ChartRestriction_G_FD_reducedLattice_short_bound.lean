-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_reducedLattice_short_bound
-- name    : ReciprocityTheory.ChartRestriction.G.FD.reducedLattice_short_bound
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T10:24:36.823121+00:00
-- url     : https://prove2.me/theorems/ef6779dd-2f33-5573-ab81-775f9c185812
-- title:
--   FD: reduced Lattice short bound
-- statement:
--   The FD construction uses the reduced Lattice short bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/ReducedLatticeShortBound.lean#L39-L285
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/ReducedLatticeShortBound.lean#L39-L285

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_ExistsPerpHermitianReduction
import Definitions.Def_ReciprocityTheory_SemistableReduction_LatAll
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_IsotropicCombinations
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_QuadraticCoefficientForms
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_ReducedLatticeShortBound
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

theorem ReciprocityTheory.ChartRestriction.G.FD.reducedLattice_short_bound (hD5 : CoveringRadiusStatement) (r : ℕ) (X : DataX E r) (ξ : Fin r → E) (z0 : Frame X.Ψ r)
    (f : X.Ψ → Fin (r - 2) → Fin r → ℂ) (β : Fin (r - 2) → Fin r → E) (S : ReciprocityTheory.MultiplicativeHeights.HermForm E (r - 2))
    (LB : Submodule (𝓞 E) (Fin (r - 2) → E)) (Q : X.Ψ → Matrix (Fin (r - 2)) (Fin (r - 2)) ℂ) (ep rh : ℝ)
    (hξ : X.IsIso ξ) (hz : z0 ∈ X.dom) (hf : X.UBasis z0 ξ f)
    (hβ : ∀ k, herm X.Gm (β k) ξ = 0)
    (hβind : LinearIndependent E (Fin.cons ξ β : Fin (r - 2 + 1) → Fin r → E))
    (hβspan : ∀ x : Fin r → E, herm X.Gm x ξ = 0 → ∃ (c : Fin (r - 2) → E) (e : E), x = ∑ k, c k • β k + e • ξ)
    (hS : ∀ c c' : Fin (r - 2) → E, S.h c c' = herm X.Gm (∑ k, c' k • β k) (∑ k, c k • β k))
    (hLB : ∀ c : Fin (r - 2) → E, c ∈ LB ↔ ∃ e : E, ∑ k, c k • β k + e • ξ ∈ X.L')
    (hLat : ReciprocityTheory.MultiplicativeHeights.IsLattice LB) (hSD : ReciprocityTheory.MultiplicativeHeights.IsSelfDual S LB)
    (hQ : ∀ τ, (Q τ).det ≠ 0)
    (hSQ : ∀ τ (c c' : Fin (r - 2) → E), τ.1 (S.h c c') =
      ReciprocityTheory.MultiplicativeHeights.jForm (X.p0 - 1) (Q τ *ᵥ ReciprocityTheory.MultiplicativeHeights.embVec τ.1 c) (Q τ *ᵥ ReciprocityTheory.MultiplicativeHeights.embVec τ.1 c'))
    (hQf : ∀ τ (c : Fin (r - 2) → E), X.ucomp z0 ξ (X.embV (∑ k, c k • β k)) τ =
      ∑ k, (Q τ *ᵥ ReciprocityTheory.MultiplicativeHeights.embVec τ.1 c) k • f τ k)
    (hep : 0 < ep) (hep1 : ep ≤ 1) (hrh : 0 < rh) (hrh1 : rh ≤ 1)
    (hD4 : ∀ x ∈ X.L', herm X.Gm x ξ = 0 → (∀ e : E, x ≠ e • ξ) →
      ∃ τ : X.Ψ, ep ≤ X.maj z0 τ (X.ucomp z0 ξ (X.embV x) τ)) :
    ∃ lam : Fin (r - 2) → Fin r → E,
      (∀ j, lam j ∈ X.L' ∧ herm X.Gm (lam j) ξ = 0) ∧
      LinearIndependent E (Fin.cons ξ lam : Fin (r - 2 + 1) → Fin r → E) ∧
      (∀ j k : Fin (r - 2), (j : ℕ) < X.p0 - 1 → X.p0 - 1 ≤ (k : ℕ) → herm X.Gm (lam j) (lam k) = 0) ∧
      (∀ j : Fin (r - 2), (j : ℕ) < X.p0 - 1 → ∀ τ : X.Ψ, 0 < (τ.1 (herm X.Gm (lam j) (lam j))).re) ∧
      (∀ j : Fin (r - 2), X.p0 - 1 ≤ (j : ℕ) → ∀ τ : X.Ψ, (τ.1 (herm X.Gm (lam j) (lam j))).re < 0) ∧
      (∀ j (τ : X.Ψ), ‖τ.1 (herm X.Gm (lam j) (lam j))‖ ≤ d6La r X.p0 (fdeg E) (dE E) ep rh ^ 2) ∧
      (∀ τ, LinearIndependent ℂ fun j => X.ucomp z0 ξ (X.embV (lam j)) τ) ∧
      (∀ τ j, X.ucomp z0 ξ (X.embV (lam j)) τ ∈ Submodule.span ℂ (Set.range (f τ))) ∧
      (∀ τ (j k : Fin (r - 2)), (j : ℕ) < X.p0 - 1 → X.p0 - 1 ≤ (k : ℕ) →
        hermC τ.1 X.Gm (X.ucomp z0 ξ (X.embV (lam j)) τ) (X.ucomp z0 ξ (X.embV (lam k)) τ) = 0) ∧
      (∀ τ (w : Fin (r - 2) → ℂ), (∀ j : Fin (r - 2), X.p0 - 1 ≤ (j : ℕ) → w j = 0) → w ≠ 0 →
        0 < (hermC τ.1 X.Gm (∑ j, w j • X.ucomp z0 ξ (X.embV (lam j)) τ)
          (∑ j, w j • X.ucomp z0 ξ (X.embV (lam j)) τ)).re) ∧
      (∀ τ (w : Fin (r - 2) → ℂ), (∀ j : Fin (r - 2), (j : ℕ) < X.p0 - 1 → w j = 0) → w ≠ 0 →
        (hermC τ.1 X.Gm (∑ j, w j • X.ucomp z0 ξ (X.embV (lam j)) τ)
          (∑ j, w j • X.ucomp z0 ξ (X.embV (lam j)) τ)).re < 0) ∧
      (∀ τ (c : Fin (r - 2) → ℂ), (∑ k, c k • f τ k) ∈ Submodule.span ℂ
          ((fun j => X.ucomp z0 ξ (X.embV (lam j)) τ) '' {j | (j : ℕ) < X.p0 - 1}) →
        (∑ k : Fin (r - 2), if (k : ℕ) < X.p0 - 1 then 0 else ‖c k‖ ^ 2) ≤
          (rh / 120) ^ 2 * ∑ k : Fin (r - 2), if (k : ℕ) < X.p0 - 1 then ‖c k‖ ^ 2 else 0) := by sorry
