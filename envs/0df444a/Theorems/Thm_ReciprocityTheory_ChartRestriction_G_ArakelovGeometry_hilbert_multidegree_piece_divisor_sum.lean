-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_hilbert_multidegree_piece_divisor_sum
-- name    : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.hilbert_multidegree_piece_divisor_sum
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T10:10:06.919601+00:00
-- url     : https://prove2.me/theorems/a585d38d-595f-54b8-8f63-0bfb4250ff03
-- title:
--   Arakelov Geometry: hilbert multidegree piece divisor sum
-- statement:
--   The Arakelov Geometry construction uses the hilbert multidegree piece divisor sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/HilbertMultidegreePieceDivisorSum.lean#L133-L175
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/HilbertMultidegreePieceDivisorSum.lean#L133-L175

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_NatCardEqPowLength
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_HilbertMultidegreePieceDivisorSum
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial
variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.hilbert_multidegree_piece_divisor_sum
    (hR4 : ∀ (n : ℕ) (V : Ideal (MRing ι)) (a : Fin (n + 1) → K → ℤ) (k : K) (i : ι k),
      IsMultiProjPrime V → charOf V ≠ 0 →
      ringKrullDim (MRing ι ⧸ V) = ((n + 1 + Fintype.card K : ℕ) : WithBot ℕ∞) →
      (X ⟨k, i⟩ : MRing ι) ∉ V →
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
