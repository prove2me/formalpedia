-- Prove2me | Theorems.Thm_ReciprocityTheory_Gal_exists_valuationSubring_over
-- name    : ReciprocityTheory.Gal.exists_valuationSubring_over
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T16:49:20.987936+00:00
-- url     : https://prove2.me/theorems/fa3d7901-de1d-4568-9b22-bea575ff21a3
-- title:
--   Gal: exists valuation Subring over
-- statement:
--   The Gal construction uses the exists valuation Subring over property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GaloisValuations/GlobalA.lean#L114-L167
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GaloisValuations/GlobalA.lean#L114-L167

import Mathlib
import Definitions.Def_ReciprocityTheory_GaloisValuations_GlobalA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Pointwise
open ReciprocityTheory ReciprocityTheory.Gal
variable {F Ω : Type*} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]

theorem ReciprocityTheory.Gal.exists_valuationSubring_over (v : HeightOneSpectrum (𝓞 F)) :
    ∃ A : ValuationSubring Ω, ∀ x : 𝓞 F,
      A.valuation (algebraMap F Ω (x : F)) < 1 ↔ x ∈ v.asIdeal := by sorry
