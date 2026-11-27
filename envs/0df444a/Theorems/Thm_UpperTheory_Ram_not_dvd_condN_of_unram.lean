-- Prove2me | Theorems.Thm_UpperTheory_Ram_not_dvd_condN_of_unram
-- name    : UpperTheory.Ram.not_dvd_condN_of_unram
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T14:38:38.226468+00:00
-- url     : https://prove2.me/theorems/11e44bf1-fae8-402b-b2ff-ef3ea0167982
-- title:
--   Ram: not dvd cond N of unram
-- statement:
--   The Ram construction uses the not dvd cond N of unram property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/CyclotomicBounds/RamifiedDiscriminants/CondSq.lean#L56-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/CyclotomicBounds/RamifiedDiscriminants/CondSq.lean#L56-L60

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_PrimeDiscriminants_RamDiscr
import Definitions.Def_Development_AutomorphicArithmetic_CyclotomicBounds_RamifiedDiscriminants_CondSq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
open UpperTheory UpperTheory.Ram
variable {R : Formalism.BasicNotions.Ranks} (H : Formalism.BasicNotions.Host R)

theorem UpperTheory.Ram.not_dvd_condN_of_unram {p : ℕ} (hp : p.Prime)
    (h : ∀ w : HeightOneSpectrum (𝓞 H.E), (p : 𝓞 H.E) ∈ w.asIdeal → (p : 𝓞 H.E) ∉ w.asIdeal ^ 2) :
    ¬ p ∣ H.QS * H.q * H.d := by sorry
