-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_hasymp_all
-- name    : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.hasymp_all
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T10:10:32.919924+00:00
-- url     : https://prove2.me/theorems/299ddd6f-b290-4b78-a4ad-3402a30e41e6
-- title:
--   Arakelov Geometry: hasymp all
-- statement:
--   The Arakelov Geometry construction uses the hasymp all property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/HasympAll.lean#L130-L158
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/HasympAll.lean#L130-L158

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_MultAtEqCount
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_HasympAll
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

theorem ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.hasymp_all {L : ℝ} {p : ℕ} (hp : p.Prime)
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
    (hbase : ∀ W : Ideal (MRing ι), IsMultiProjPrime W → (p : MRing ι) ∈ W →
      ringKrullDim (MRing ι ⧸ W) = ((0 + Fintype.card K : ℕ) : WithBot ℕ∞) → HAsymp L 0 W) :
    ∀ (d : ℕ) (W : Ideal (MRing ι)), IsMultiProjPrime W → (p : MRing ι) ∈ W →
      ringKrullDim (MRing ι ⧸ W) = ((d + Fintype.card K : ℕ) : WithBot ℕ∞) →
      HAsymp L d W ∧ SymmAt d W := by sorry
