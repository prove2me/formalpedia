-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_ct_iter_single_eq_polyDeriv
-- name    : ReciprocityTheory.ChartRestriction.G.I2.ct_iter_single_eq_polyDeriv
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T10:28:56.465302+00:00
-- url     : https://prove2.me/theorems/56f939b8-1142-4b9d-a590-622db9c4a739
-- title:
--   I2: ct iter single eq poly Deriv
-- statement:
--   The I2 construction uses the ct iter single eq poly Deriv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/ColTorusA.lean#L200-L214
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/ColTorusA.lean#L200-L214

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_PolyDerivMonomialOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_ColTorusA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2
open Complex
noncomputable section

theorem ReciprocityTheory.ChartRestriction.G.I2.ct_iter_single_eq_polyDeriv {ι : Type} [Fintype ι] [DecidableEq ι] (F : EuclideanSpace ℂ ι → ℂ)
    (hF : ContDiff ℂ (⊤ : ℕ∞) F) (j : ℕ) (v : Fin j → ι) :
    iteratedFDeriv ℂ j F 0 (fun k => EuclideanSpace.single (v k) (1 : ℂ)) =
      polyDeriv (MvPolynomial.monomial (Multiset.toFinsupp (↑(List.ofFn v) : Multiset ι)) (1 : ℂ))
        (fun i => EuclideanSpace.single i (1 : ℂ)) F 0 := by sorry
