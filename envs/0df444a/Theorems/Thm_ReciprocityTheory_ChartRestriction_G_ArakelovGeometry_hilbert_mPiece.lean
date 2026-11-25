-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_hilbert_mPiece
-- name    : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.hilbert_mPiece
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T14:13:55.182261+00:00
-- url     : https://prove2.me/theorems/3619cc8c-58f8-437a-b2ea-594617595d73
-- title:
--   Arakelov Geometry: hilbert m Piece
-- statement:
--   The Arakelov Geometry construction uses the hilbert m Piece property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/ExistsMPrimeFiltration.lean#L20-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/ExistsMPrimeFiltration.lean#L20-L37

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_HilbertMultidegreePieceDivisorSum
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_ExistsMPrimeFiltration
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.GeometryOfNumbersTheory MvPolynomial MeasureTheory Module Filter Asymptotics
open scoped ComplexOrder
variable {Ω : Type} [Field Ω] [CharZero Ω] {κ : Type} [Fintype κ] {D : ℕ}

theorem ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.hilbert_mPiece {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
    (hR4 : ∀ (n : ℕ) (V : Ideal (MRing ι)) (a : Fin (n + 1) → K → ℤ) (k : K) (i : ι k),
      IsMultiProjPrime V → charOf V ≠ 0 →
      ringKrullDim (MRing ι ⧸ V) = ((n + 1 + Fintype.card K : ℕ) : WithBot ℕ∞) → (X ⟨k, i⟩ : MRing ι) ∉ V →
      (a (Fin.last n) = fun k' => if k' = k then 1 else 0) →
      geoNum (n + 1) V a = ∑ᶠ W' ∈ divSupp V (X ⟨k, i⟩),
        (multAt (V ⊔ Ideal.span {(X ⟨k, i⟩ : MRing ι)}) W' : ℤ) * geoNum n W' (Fin.init a))
    (hSymm : ∀ (n : ℕ) (V : Ideal (MRing ι)) (a : Fin n → K → ℤ) (σ : Equiv.Perm (Fin n)),
      IsMultiProjPrime V → charOf V ≠ 0 →
      ringKrullDim (MRing ι ⧸ V) = ((n + Fintype.card K : ℕ) : WithBot ℕ∞) →
      geoNum n V (a ∘ σ) = geoNum n V a)
    (W : Ideal (MRing ι)) (hW : IsMultiProjPrime W) (hp : (charOf W).Prime) (d : ℕ)
    (hd : ringKrullDim (MRing ι ⧸ W) = ((d + Fintype.card K : ℕ) : WithBot ℕ∞)) :
    ∃ (a₀ : ℕ) (C : ℝ), ∀ a : K → ℕ, (∀ k, a₀ ≤ a k) →
      |Real.log (Nat.card (mPiece W a)) / Real.log (charOf W) -
          (geoNum d W (fun _ k => (a k : ℤ)) : ℝ) / (d.factorial : ℝ)| ≤
        C * ((∑ k, a k : ℕ) + 1 : ℝ) ^ d / ((∑ k, a k : ℕ) + 1 : ℝ) := by sorry
