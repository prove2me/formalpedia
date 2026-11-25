-- Prove2me | Theorems.Thm_UpperTheory_Ram_exists_place_over
-- name    : UpperTheory.Ram.exists_place_over
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T11:12:25.803038+00:00
-- url     : https://prove2.me/theorems/9ecb4fe2-c91e-59ae-adff-8d81a24b1c5b
-- title:
--   Ram: exists place over
-- statement:
--   The Ram construction uses the exists place over property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/CyclotomicBounds/RamifiedDiscriminants/CondSq.lean#L40-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/CyclotomicBounds/RamifiedDiscriminants/CondSq.lean#L40-L54

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

theorem UpperTheory.Ram.exists_place_over (E : Type) [Field E] [NumberField E] {p : ℕ} (hp : p.Prime) :
    ∃ w : HeightOneSpectrum (𝓞 E), (p : 𝓞 E) ∈ w.asIdeal := by sorry
