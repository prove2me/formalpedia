-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_cab_jet_eq
-- name    : ReciprocityTheory.ChartRestriction.G.I2.cab_jet_eq
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T10:28:53.849948+00:00
-- url     : https://prove2.me/theorems/c352e141-bc24-4319-a799-b1605ff164ec
-- title:
--   I2: cab jet eq
-- statement:
--   The I2 construction uses the cab jet eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/ColAbelA.lean#L76-L120
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/ColAbelA.lean#L76-L120

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_SplitSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_PropASt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_RCauchy
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_ContDiffOfDifferentiableFd
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_ColAbelA
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

theorem ReciprocityTheory.ChartRestriction.G.I2.cab_jet_eq {ι : Type} [Fintype ι] [DecidableEq ι] {c : ℕ} {β P : EuclideanSpace ℂ ι → ℂ}
    (hβ : ContDiff ℂ (⊤ : WithTop ℕ∞) β) (hP : ContDiff ℂ (⊤ : WithTop ℕ∞) P)
    (h : ∀ α : ι →₀ ℕ, α.degree ≤ c →
      polyDeriv (MvPolynomial.monomial α 1) (fun i => EuclideanSpace.single i 1) β 0 =
        polyDeriv (MvPolynomial.monomial α 1) (fun i => EuclideanSpace.single i 1) P 0) :
    iteratedFDeriv ℂ c β 0 = iteratedFDeriv ℂ c P 0 := by sorry
