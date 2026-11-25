-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_colL_coe
-- name    : ReciprocityTheory.ChartRestriction.G.I2.colL_coe
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T14:14:32.304943+00:00
-- url     : https://prove2.me/theorems/4948f59f-5ef1-45ad-b9d3-62a943fecf46
-- title:
--   I2: col L coe
-- statement:
--   The I2 construction uses the col L coe property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/PolyDerivDeterminantPolyTensor.lean#L101-L108
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/PolyDerivDeterminantPolyTensor.lean#L101-L108

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_L2NormFundamentalDomain
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_PolyDerivDeterminantPolyTensor
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2
open MvPolynomial
noncomputable section
variable {E : Type} [Field E] [NumberField E] {n nb : ℕ} {dim : (E →+* ℂ) → ℕ}
variable (X : PT E) (bs : Fin nb → Block E n X.dim)
open Classical

theorem ReciprocityTheory.ChartRestriction.G.I2.colL_coe (T : Choice bs) (k : Fin n) :
    ((colL (lst X bs T) k : List (Vsp X.dim)) : Multiset (Vsp X.dim)) =
      ((Multiset.map (letter bs T) Finset.univ.val).filter (fun l => l.1 = k)).map
        (fun l => EuclideanSpace.single l.2 (1 : ℂ)) := by sorry
