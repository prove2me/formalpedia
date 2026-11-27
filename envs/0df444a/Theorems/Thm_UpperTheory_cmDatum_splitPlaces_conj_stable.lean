-- Prove2me | Theorems.Thm_UpperTheory_cmDatum_splitPlaces_conj_stable
-- name    : UpperTheory.cmDatum_splitPlaces_conj_stable
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T14:50:56.843863+00:00
-- url     : https://prove2.me/theorems/5d63f007-00b6-4ae3-a6f5-6a627f15fbfb
-- title:
--   Upper Theory: cm Datum split Places conj stable
-- statement:
--   The Upper Theory construction uses the cm Datum split Places conj stable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/CMTraceForms/CmDatumSplitPlacesConjStable.lean#L101-L233
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/CMTraceForms/CmDatumSplitPlacesConjStable.lean#L101-L233

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_CMTraceForms_Places
import Definitions.Def_Development_AutomorphicArithmetic_CMTraceForms_CmDatumSplitPlacesConjStable
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

theorem UpperTheory.cmDatum_splitPlaces_conj_stable :
    ∀ (p : ℕ), p.Prime → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E), SplitAt H.d p →
      ∀ (C : Type) [Field C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C], v.Integers O → ¬ IsUnit (p : O) →
      (∀ σ : 𝓞 E →+* O, IsUnit (σ H.w0 - σ (H.bar H.w0))) ∧ ∀ x : O, x ≠ 0 → ∃ N : ℕ, v (N : C) < v (algebraMap O C x) ∧
        ∀ σ : 𝓞 E →+* O, ∃ a : 𝓞 E, H.bar a * a = (N : 𝓞 E) ∧ v (algebraMap O C (σ a - 1)) < v (algebraMap O C x) := by sorry
