-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_dim_quot_minimal_add_one
-- name    : ReciprocityTheory.ChartRestriction.G.Geo.dim_quot_minimal_add_one
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T23:58:58.243924+00:00
-- url     : https://prove2.me/theorems/98be4781-e6bc-4bc1-8318-b45b7a3fb757
-- title:
--   Geo: dim quot minimal add one
-- statement:
--   The Geo construction uses the dim quot minimal add one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/InterDivSupp.lean#L14-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/InterDivSupp.lean#L14-L38

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivSuppA
import Definitions.Def_Lemmata_GeneralBFactTerForm_Imports
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivSupp
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
open MvPolynomial
variable {σ : Type*} [Finite σ]

theorem ReciprocityTheory.ChartRestriction.G.Geo.dim_quot_minimal_add_one (P W : Ideal (MvPolynomial σ ℤ)) [P.IsPrime]
    (s : MvPolynomial σ ℤ) (hs : s ∉ P) (hW : W ∈ (P ⊔ Ideal.span {s}).minimalPrimes) :
    ringKrullDim (MvPolynomial σ ℤ ⧸ W) + 1 = ringKrullDim (MvPolynomial σ ℤ ⧸ P) := by sorry
