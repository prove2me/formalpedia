-- Prove2me | Theorems.Thm_UpperTheory_discr_CMDatum_eq_prod_places
-- name    : UpperTheory.discr_CMDatum_eq_prod_places
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T11:14:00.209494+00:00
-- url     : https://prove2.me/theorems/922f8043-2320-4aca-b4b6-87eaf4264054
-- title:
--   Upper Theory: discr CMDatum eq prod places
-- statement:
--   The Upper Theory construction uses the discr CMDatum eq prod places property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/CMTraceForms/DiscrCMDatumEqProdPlaces.lean#L251-L484
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/CMTraceForms/DiscrCMDatumEqProdPlaces.lean#L251-L484

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_CMTraceForms_Places
import Definitions.Def_Development_AutomorphicArithmetic_CMTraceForms_DiscrCMDatumEqProdPlaces
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs Formalism.L2.Pj UpperTheory.Depth
open UpperTheory.PlacesDiscr

theorem UpperTheory.discr_CMDatum_eq_prod_places :
    ∀ (E : Type) [Field E] [NumberField E] [StarRing (𝓞 E)] (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C], v.Integers O → ∀ [Fact (¬ IsUnit (p : O))] [Algebra ℤ_[p] O]
      (s : ℕ) (w : Fin s → Place p (𝓞 E)), (∀ i j, i ≠ j → (w i).e * (w j).e = 0) → (∑ i, (w i).e) + (∑ i, (w i).bar) = 1 →
      (∀ i j, (w i).e * (w j).bar = 0) →
      2 * ∑ i, (w i).n = Module.finrank ℚ E ∧ ∀ t : ∀ i, Fin (w i).n ≃ Emb (O := O) (w i).e, ∃ vdi : Fin s → ℝ,
        (∀ i, HasVd p v (w i) (t i) (vdi i)) ∧
        ∑ i, ((w i).n : ℝ) * vdi i = (padicValInt p (NumberField.discr E) : ℝ) / 2 := by sorry
