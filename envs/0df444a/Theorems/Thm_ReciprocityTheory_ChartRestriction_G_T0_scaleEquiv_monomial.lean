-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_scaleEquiv_monomial
-- name    : ReciprocityTheory.ChartRestriction.G.T0.scaleEquiv_monomial
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:50:46.896378+00:00
-- url     : https://prove2.me/theorems/c8e1a58f-f867-41e7-9ee8-64c14967a159
-- title:
--   T0: scale Equiv monomial
-- statement:
--   The T0 construction uses the scale Equiv monomial property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/ScaleMultiHomogeneous.lean#L40-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/ScaleMultiHomogeneous.lean#L40-L58

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HtDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ScaleMultiHomogeneous
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open MvPolynomial
variable {S σ : Type*} [CommRing S]

theorem ReciprocityTheory.ChartRestriction.G.T0.scaleEquiv_monomial [Fintype σ] (P : σ → Prop) [DecidablePred P] (u : Sˣ)
    (s : σ →₀ ℕ) (a : S) :
    scaleEquiv P u (monomial s a) =
      C ((u : S) ^ (∑ v ∈ Finset.univ.filter P, s v)) * monomial s a := by sorry
