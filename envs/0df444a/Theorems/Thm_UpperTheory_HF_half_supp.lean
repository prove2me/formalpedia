-- Prove2me | Theorems.Thm_UpperTheory_HF_half_supp
-- name    : UpperTheory.HF.half_supp
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T11:19:39.469799+00:00
-- url     : https://prove2.me/theorems/b16c2874-094f-5e15-8010-47f1de152486
-- title:
--   HF: half supp
-- statement:
--   The HF construction uses the half supp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/FrobeniusLocalisation/halfSupp.lean#L10-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/FrobeniusLocalisation/halfSupp.lean#L10-L64

import Definitions.Def_Development_AutomorphicArithmetic_FrobeniusLocalisation_DiffDefs
import Definitions.Def_Development_AutomorphicArithmetic_FrobeniusLocalisation_DiffEKSupp
import Definitions.Def_Development_AutomorphicArithmetic_FrobeniusLocalisation_DiscrK
import Definitions.Def_Development_AutomorphicArithmetic_FrobeniusLocalisation_halfSupp
import Theorems.Thm_Formalism_FrobeniusOrbits_Final_conj

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

theorem UpperTheory.HF.half_supp :
    ∀ {φ : Frame} (H : HostAx φ) (𝔟 : Ideal (𝓞 H.E)), differentIdeal (𝓞 H.K) (𝓞 H.E) = 𝔟 * (H.conj • 𝔟) → 𝔟 ⊔ H.conj • 𝔟 = ⊤ → (∀ (P : Ideal (𝓞 H.E)) [P.IsPrime], ((P ∣ 𝔟 ∨ H.conj • P ∣ 𝔟) ↔ ∃ l ∈ H.ramI, P.LiesOver (span {(l : ℤ)})) ∧ ¬ (P ∣ 𝔟 ∧ H.conj • P ∣ 𝔟) ∧ (P ∣ 𝔟 → multiplicity P 𝔟 = multiplicity P (differentIdeal (𝓞 H.K) (𝓞 H.E)))) ∧ ∃ s : 𝓞 H.E, (s : H.E) = H.sqd ∧ differentIdeal ℤ (𝓞 H.E) = 𝔟 * (H.conj • 𝔟) * span {s} := by sorry
