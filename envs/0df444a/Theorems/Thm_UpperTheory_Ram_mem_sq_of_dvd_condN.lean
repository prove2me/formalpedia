-- Prove2me | Theorems.Thm_UpperTheory_Ram_mem_sq_of_dvd_condN
-- name    : UpperTheory.Ram.mem_sq_of_dvd_condN
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T11:13:41.241786+00:00
-- url     : https://prove2.me/theorems/29c779b2-ec5e-46d6-9070-d5d89b2dae97
-- title:
--   Ram: mem sq of dvd cond N
-- statement:
--   The Ram construction uses the mem sq of dvd cond N property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/CyclotomicBounds/RamifiedDiscriminants/CondSq.lean#L31-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/CyclotomicBounds/RamifiedDiscriminants/CondSq.lean#L31-L38

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

theorem UpperTheory.Ram.mem_sq_of_dvd_condN {p : ℕ} (hp : p.Prime) (h : p ∣ H.QS * H.q * H.d) (P : Ideal (𝓞 H.E)) (hP : P.IsPrime)
    (hv : (p : 𝓞 H.E) ∈ P) : (p : 𝓞 H.E) ∈ P ^ 2 := by sorry
