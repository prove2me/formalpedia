-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_SatakeVectors_gauss_int
-- name    : ReciprocityTheory.ChartRestriction.G.T0.SatakeVectors.gauss_int
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-27T05:48:47.938912+00:00
-- url     : https://prove2.me/theorems/1ede6118-8398-49b2-8837-ff62b27ae9ae
-- title:
--   Satake Vectors: gauss int
-- statement:
--   The Satake Vectors construction uses the gauss int property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/ExistsIntMultiple.lean#L93-L128
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/ExistsIntMultiple.lean#L93-L128

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_GaussAbsMulSupportFinite
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ExistsIntMultiple
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0 ReciprocityTheory.ChartRestriction.G.T0.SatakeVectors
open NumberField IsDedekindDomain
variable {K : Type} [Field K] [NumberField K]

theorem ReciprocityTheory.ChartRestriction.G.T0.SatakeVectors.gauss_int {κ : Type} [Fintype κ] [DecidableEq κ] (G₀ : MvPolynomial κ (𝓞 K))
    (hG : G₀ ≠ 0) (S T : Finset (κ →₀ ℕ)) {r : ℕ} (e : T ≃ Fin r)
    (hST : ∀ m ∈ S, (MvPolynomial.map (algebraMap (𝓞 K) K) G₀ * MvPolynomial.monomial m 1).support ⊆ T)
    (p : Fin S.card → K)
    (hint : ∀ i, ∃ y : 𝓞 K, (y : K) =
      coordVec e (MvPolynomial.map (algebraMap (𝓞 K) K) G₀ * polyOf S p) i)
    (j : Fin S.card) (s : κ →₀ ℕ) : ∃ y : 𝓞 K, (y : K) = p j * ((G₀.coeff s : 𝓞 K) : K) := by sorry
