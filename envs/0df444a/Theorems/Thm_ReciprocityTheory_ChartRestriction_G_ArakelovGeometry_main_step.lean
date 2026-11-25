-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_main_step
-- name    : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.main_step
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T10:10:52.006258+00:00
-- url     : https://prove2.me/theorems/2e45a77d-66e2-4794-a9dd-dfc63daab9e3
-- title:
--   Arakelov Geometry: main step
-- statement:
--   The Arakelov Geometry construction uses the main step property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/HasympAll.lean#L11-L128
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/HasympAll.lean#L11-L128

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

theorem ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.main_step {L : ℝ} {m p : ℕ} (hp : p.Prime) {W : Ideal (MRing ι)} (hW : IsMultiProjPrime W)
    (hpW : (p : MRing ι) ∈ W)
    (hdim : ringKrullDim (MRing ι ⧸ W) = ((m + 1 + Fintype.card K : ℕ) : WithBot ℕ∞))
    (hR4W : ∀ (a : Fin (m + 1) → K → ℤ) (k : K) (i : ι k), (X ⟨k, i⟩ : MRing ι) ∉ W →
      (a (Fin.last m) = fun k' => if k' = k then 1 else 0) →
      geoNum (m + 1) W a = ∑ᶠ W' ∈ divSupp W (X ⟨k, i⟩),
        (multAt (W ⊔ Ideal.span {(X ⟨k, i⟩ : MRing ι)}) W' : ℤ) * geoNum m W' (Fin.init a))
    (hSW : SymmAt (m + 1) W)
    (IH : ∀ W' : Ideal (MRing ι), IsMultiProjPrime W' → (p : MRing ι) ∈ W' →
      ringKrullDim (MRing ι ⧸ W') = ((m + Fintype.card K : ℕ) : WithBot ℕ∞) →
      HAsymp L m W' ∧ SymmAt m W') :
    HAsymp L (m + 1) W := by sorry
