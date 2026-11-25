-- Prove2me | Theorems.Thm_UpperTheory_HF_diff_EK_supp
-- name    : UpperTheory.HF.diff_EK_supp
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T11:17:58.637919+00:00
-- url     : https://prove2.me/theorems/dfd63e80-fbb2-578e-976c-43ff62d79344
-- title:
--   HF: diff EK supp
-- statement:
--   The HF construction uses the diff EK supp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/FrobeniusLocalisation/DiffEKSupp.lean#L26-L90
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/FrobeniusLocalisation/DiffEKSupp.lean#L26-L90

import Definitions.Def_Development_AutomorphicArithmetic_FrobeniusLocalisation_DiffDefs
import Definitions.Def_Development_AutomorphicArithmetic_FrobeniusLocalisation_DiffMult
import Definitions.Def_Development_AutomorphicArithmetic_FrobeniusLocalisation_MemRam
import Definitions.Def_Development_AutomorphicArithmetic_FrobeniusLocalisation_DiscrK
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_KcDiff
import Definitions.Def_Development_AutomorphicArithmetic_FrobeniusLocalisation_DiffEKSupp
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open UpperTheory.HF
open NumberField Ideal Formalism.HC Formalism.FrobeniusOrbits
open scoped Pointwise

theorem UpperTheory.HF.diff_EK_supp :
    ∀ {φ : Frame} (H : HostAx φ), (∀ σ : H.E ≃ₐ[ℚ] H.E, σ • differentIdeal (𝓞 H.K) (𝓞 H.E) = differentIdeal (𝓞 H.K) (𝓞 H.E)) ∧ (∀ (P : Ideal (𝓞 H.E)) [P.IsPrime], P ∣ differentIdeal (𝓞 H.K) (𝓞 H.E) ↔ ∃ l ∈ H.ramI, P.LiesOver (span {(l : ℤ)})) ∧ (∀ l : ℕ, l.Prime → l ≠ H.d → ∀ (P : Ideal (𝓞 H.E)) [P.IsPrime] [P.LiesOver (span {(l : ℤ)})], (multiplicity P (differentIdeal (𝓞 H.K) (𝓞 H.E)) : ℝ) = H.el l * H.vdH l) ∧ 2 ∈ H.ramI := by sorry
