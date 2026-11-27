-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_SatakeVectors_log_relIndex_le
-- name    : ReciprocityTheory.ChartRestriction.G.T0.SatakeVectors.log_relIndex_le
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-27T05:46:38.892393+00:00
-- url     : https://prove2.me/theorems/2dcd74fc-b22e-498f-b92d-f99afcd2820a
-- title:
--   Satake Vectors: log rel Index le
-- statement:
--   The Satake Vectors construction uses the log rel Index le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/ExistsIntMultiple.lean#L168-L258
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/ExistsIntMultiple.lean#L168-L258

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
open scoped nonZeroDivisors
variable {K : Type} [Field K] [NumberField K]

theorem ReciprocityTheory.ChartRestriction.G.T0.SatakeVectors.log_relIndex_le {κ : Type} [Fintype κ] [DecidableEq κ] (G₀ : MvPolynomial κ (𝓞 K))
    (hG : G₀ ≠ 0) (S T : Finset (κ →₀ ℕ)) {r : ℕ} (e : T ≃ Fin r)
    (hST : ∀ m ∈ S,
      (MvPolynomial.map (algebraMap (𝓞 K) K) G₀ * MvPolynomial.monomial m 1).support ⊆ T) :
    Real.log ((Submodule.span (𝓞 K)
        (Set.range (bG (MvPolynomial.map (algebraMap (𝓞 K) K) G₀) S e))).toAddSubgroup.relIndex
      (ReciprocityTheory.MultiplicativeHeights.satSub (stdLat K r)
        (bG (MvPolynomial.map (algebraMap (𝓞 K) K) G₀) S e)).toAddSubgroup : ℝ) ≤
      S.card * Real.log (Ideal.absNorm (contId G₀) : ℝ) := by sorry
