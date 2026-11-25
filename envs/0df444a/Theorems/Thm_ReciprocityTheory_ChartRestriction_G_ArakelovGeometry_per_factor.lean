-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_per_factor
-- name    : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.per_factor
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T10:14:38.867934+00:00
-- url     : https://prove2.me/theorems/44533a8c-b48f-54ea-8d91-0c7fe0dcd8de
-- title:
--   Arakelov Geometry: per factor
-- statement:
--   The Arakelov Geometry construction uses the per factor property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/DimOfMinimal.lean#L69-L166
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/DimOfMinimal.lean#L69-L166

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_IsMultiHomogX
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_DimOfMinimal
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
open Classical

theorem ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.per_factor {L : ℝ} {m p : ℕ} (hp : p.Prime) {W : Ideal (MRing ι)} [hWp : W.IsPrime]
    (hWm : IsMultiHomogIdeal W) (hpW : (p : MRing ι) ∈ W)
    (hdim : ringKrullDim (MRing ι ⧸ W) = ((m + 1 + Fintype.card K : ℕ) : WithBot ℕ∞))
    {s : MRing ι} {cs : K → ℕ} (hs : IsMultiHomog s cs) (hsW : s ∉ W)
    (IH : ∀ W' : Ideal (MRing ι), IsMultiProjPrime W' → (p : MRing ι) ∈ W' →
      ringKrullDim (MRing ι ⧸ W') = ((m + Fintype.card K : ℕ) : WithBot ℕ∞) →
      HAsymp L m W' ∧ SymmAt m W')
    {q : Ideal (MRing ι)} (hq : q.IsPrime) (hqm : IsMultiHomogIdeal q)
    (hJq : W ⊔ Ideal.span {s} ≤ q) (c : K → ℕ) :
    ∃ (a₀ : ℕ) (C : ℝ), 0 ≤ C ∧ ∀ a : K → ℕ, (∀ k, a₀ ≤ a k) →
      |lg q (a - c) - (if q ∈ divSupp W s then appr L m q a else 0)| ≤
        C * m * ((tdeg a : ℝ) + 1) ^ (m - 1) := by sorry
