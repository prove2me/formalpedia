-- Prove2me | Theorems.Thm_ReciprocityTheory_Gal_sum_locDegree
-- name    : ReciprocityTheory.Gal.sum_locDegree
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T10:53:04.901224+00:00
-- url     : https://prove2.me/theorems/d5f12751-3912-43d7-99d5-a91a177ff3ab
-- title:
--   Gal: sum loc Degree
-- statement:
--   The Gal construction uses the sum loc Degree property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GaloisValuations/ArithOfA.lean#L42-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GaloisValuations/ArithOfA.lean#L42-L77

import Definitions.Def_ReciprocityTheory_GaloisValuations_Global
import Definitions.Def_ReciprocityTheory_GaloisValuations_ArithOfA
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
open Formalism.ConjugateSelfDual
variable {F : Type*} [Field F] [NumberField F]

theorem ReciprocityTheory.Gal.sum_locDegree (l : ℕ) [Fact l.Prime] (T : Finset (HeightOneSpectrum (𝓞 F)))
    (hT : ∀ v, v ∈ T ↔ ((l : ℕ) : 𝓞 F) ∈ v.asIdeal) :
    ∑ v ∈ T, locDegree v = Module.finrank ℚ F := by sorry
