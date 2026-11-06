-- Prove2me | Theorems.Thm_TIESched_lemma_A_1
-- name    : TIESched.lemma_A_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T00:45:32.802054+00:00
-- url     : https://prove2.me/theorems/565fdd40-c385-487f-9bda-22578e0bf16c
-- title:
--   Lemma A.1 — compatible positive integration exists
-- statement:
--   There is a family of real functionals $I_D$, one for each dimension $D$, defined on all bounded compactly supported real functions on $\mathbb R^D$, that is linear, positive, translation invariant, agrees with the Lebesgue integral on continuous compactly supported functions and on indicators of bounded boxes (with any choice of endpoints), and is compatible across coordinate subsets.
--
--   It replaces the smoothing integrals of §5.4 when the mechanism is not measurable.
--
--   Differences from the source:
--   - reading: a normalized product kernel in property (5) → factors that are continuous, compactly supported and of integral one (no sign condition); reason: normalized means integral one; the proof (p.40) removes each inactive factor by its integral and uses no sign
--   - encoding: I_D defined on bounded compactly supported functions → a total function I D with properties (1)–(3) and (5) required on such functions only; reason: values elsewhere are never used
--   - encoding: the remaining coordinates, in their inherited order → the range of an order embedding e : Fin D′ ↪o Fin D, averaged function s ↦ f(s ∘ e), identity required when the reduced integrand is bounded and compactly supported; reason: a subset of coordinates with its inherited order is the range of a unique order embedding, and I_{D′} is defined only on that domain
-- source:
--   Wang, Xu, Zhang, Tight Analysis of Randomized Truthful Scheduling: An (m+1)/2 Lower Bound, arXiv:2611.05142 (artifact sha256 a89db2da…), Lemma A.1, p.39

import Mathlib
import Definitions.Def_TIESched_IsCompatibleIntegration

set_option autoImplicit false

namespace TIESched

/-- **Lemma A.1 (Compatible positive integration)** (Wang, Xu, Zhang, arXiv:2611.05142, Lemma A.1,
p.39). For every dimension `D` there is a real-valued functional `I_D` on all bounded compactly
supported real functions on `ℝ^D`, and these functionals can be chosen to satisfy linearity,
positivity, translation invariance, agreement with ordinary integration (on continuous compactly
supported functions and on indicators of bounded boxes with any choice of endpoints) and
compatibility across coordinate subsets (`IsCompatibleIntegration`). -/
theorem lemma_A_1 : ∃ I : (D : ℕ) → ((Fin D → ℝ) → ℝ) → ℝ, IsCompatibleIntegration I := by sorry

end TIESched
