-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_ct_jet_one_iter
-- name    : ReciprocityTheory.ChartRestriction.G.I2.ct_jet_one_iter
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T10:29:10.776799+00:00
-- url     : https://prove2.me/theorems/7e6474d0-3dc8-41c9-8bfe-91c96fc3130a
-- title:
--   I2: ct jet one iter
-- statement:
--   The I2 construction uses the ct jet one iter property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/ColTorusA.lean#L228-L260
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/ColTorusA.lean#L228-L260

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
open Classical

theorem ReciprocityTheory.ChartRestriction.G.I2.ct_jet_one_iter {ι : Type} [Fintype ι] (β : EuclideanSpace ℂ ι → ℂ)
    (hβ : ContDiff ℂ (⊤ : ℕ∞) β) (c : ℕ)
    (hjet : ∀ α : ι →₀ ℕ, α.degree ≤ c →
      polyDeriv (MvPolynomial.monomial α 1) (fun i => EuclideanSpace.single i 1) β 0 =
        polyDeriv (MvPolynomial.monomial α 1) (fun i => EuclideanSpace.single i 1)
          (fun v : EuclideanSpace ℂ ι => MvPolynomial.eval (fun i => v i) (1 : MvPolynomial ι ℂ)) 0) :
    β 0 = 1 ∧ ∀ j, 1 ≤ j → j ≤ c → iteratedFDeriv ℂ j β 0 = 0 := by sorry
