-- Prove2me | Theorems.Thm_ReciprocityTheory_Gal_exists_frob_over
-- name    : ReciprocityTheory.Gal.exists_frob_over
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T09:19:38.265587+00:00
-- url     : https://prove2.me/theorems/33a6cb69-523f-4e33-ba14-4d6b568abb0f
-- title:
--   Gal: exists frob over
-- statement:
--   The Gal construction uses the exists frob over property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GaloisValuations/GlobalB.lean#L238-L310
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GaloisValuations/GlobalB.lean#L238-L310

import Definitions.Def_ReciprocityTheory_GaloisValuations_GlobalA
import Definitions.Def_ReciprocityTheory_GaloisValuations_GlobalB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option linter.style.haveILetI false
noncomputable section
open NumberField IsDedekindDomain Pointwise
open scoped nonZeroDivisors
open ReciprocityTheory ReciprocityTheory.Gal
variable {F Ω : Type*} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]

theorem ReciprocityTheory.Gal.exists_frob_over {A : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 F)}
    (hA : ∀ x : 𝓞 F, A.valuation (algebraMap F Ω (x : F)) < 1 ↔ x ∈ v.asIdeal) :
    ∃ σ : Ω ≃ₐ[F] Ω, σ • A = A ∧ ∀ x, A.valuation x ≤ 1 →
      A.valuation (σ x - x ^ Nat.card (𝓞 F ⧸ v.asIdeal)) < 1 := by sorry
