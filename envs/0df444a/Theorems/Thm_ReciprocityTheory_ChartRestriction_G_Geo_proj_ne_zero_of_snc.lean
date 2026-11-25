-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_proj_ne_zero_of_snc
-- name    : ReciprocityTheory.ChartRestriction.G.Geo.proj_ne_zero_of_snc
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T10:27:08.716981+00:00
-- url     : https://prove2.me/theorems/d19b2bb2-24f9-4c60-a74b-b012209d5dd2
-- title:
--   Geo: proj ne zero of snc
-- statement:
--   The Geo construction uses the proj ne zero of snc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/InterDivPushB.lean#L55-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/InterDivPushB.lean#L55-L64

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivPushA
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_SNCAtlas
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivPushB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo
open MvPolynomial MeasureTheory ReciprocityTheory.AnForm.M
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem ReciprocityTheory.ChartRestriction.G.Geo.proj_ne_zero_of_snc {P J : Ideal (MRing ι)} {e n : ℕ} (R : AnLogRes P J e) {A : HermLine ι}
    {s : MRing ι} {r : ℕ} {m : Fin r → ℕ} {W : Fin r → Set R.X}
    {Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ)}
    (hsnc : IsSNC R.A (potOf R A) (fun x y => eval (R.lift x y) (map (Int.castRingHom ℂ) s)) m W)
    (hΨ : ∀ W' ∈ divSupp P s, IsHorizontal W' → IsGoodProj W' Ψ) {k : Fin r} (hm : m k ≠ 0)
    {x : R.X} (hx : x ∈ W k) : Ψ (segre (R.lift x x)) ≠ 0 := by sorry
