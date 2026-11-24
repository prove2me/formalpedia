-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_R_ringKrullDim_of_mem_minimalPrimes_extC
-- name    : ReciprocityTheory.AnForm.R.ringKrullDim_of_mem_minimalPrimes_extC
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T00:05:06.484503+00:00
-- url     : https://prove2.me/theorems/cbc481da-a3af-4fca-991c-3166b09b3017
-- title:
--   R: ring Krull Dim of mem minimal Primes ext C
-- statement:
--   The R construction uses the ring Krull Dim of mem minimal Primes ext C property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/BaseChangeC.lean#L46-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/BaseChangeC.lean#L46-L54

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_BaseChangeCB
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_BaseChangeC
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.R
open MvPolynomial
variable {σ : Type} [Fintype σ]

theorem ReciprocityTheory.AnForm.R.ringKrullDim_of_mem_minimalPrimes_extC (𝔭 : Ideal (MvPolynomial σ ℚ)) [𝔭.IsPrime]
    (Q : Ideal (MvPolynomial σ ℂ)) (hQ : Q ∈ (extC 𝔭).minimalPrimes) :
    ringKrullDim (MvPolynomial σ ℂ ⧸ Q) = ringKrullDim (MvPolynomial σ ℚ ⧸ 𝔭) := by sorry
