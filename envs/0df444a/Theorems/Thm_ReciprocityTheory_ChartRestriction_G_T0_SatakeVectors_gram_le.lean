-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_SatakeVectors_gram_le
-- name    : ReciprocityTheory.ChartRestriction.G.T0.SatakeVectors.gram_le
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-27T05:48:37.729735+00:00
-- url     : https://prove2.me/theorems/e1ffc2bb-b17c-42e9-8ac1-7b6698587cde
-- title:
--   Satake Vectors: gram le
-- statement:
--   The Satake Vectors construction uses the gram le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/ExistsIntMultiple.lean#L280-L311
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/ExistsIntMultiple.lean#L280-L311

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
open NumberField
variable {K : Type} [Field K] [NumberField K]

theorem ReciprocityTheory.ChartRestriction.G.T0.SatakeVectors.gram_le {κ : Type} [Fintype κ] [DecidableEq κ] (G : MvPolynomial κ K) (hG : G ≠ 0)
    (S T : Finset (κ →₀ ℕ)) {r : ℕ} (e : T ≃ Fin r)
    (hST : ∀ m ∈ S, (G * MvPolynomial.monomial m 1).support ⊆ T) (σ : K →+* ℂ) :
    2 * (S.card : ℝ) * ReciprocityTheory.MultiplicativeHeights.torusMean (MvPolynomial.map σ G) ≤
      Real.log (ReciprocityTheory.MultiplicativeHeights.gramC (1 : Matrix (Fin r) (Fin r) ℂ) σ (bG G S e)).det.re := by sorry
