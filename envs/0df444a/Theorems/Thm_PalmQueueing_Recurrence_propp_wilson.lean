-- Prove2me | Theorems.Thm_PalmQueueing_Recurrence_propp_wilson
-- name    : PalmQueueing.Recurrence.propp_wilson
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-02T00:17:09.60729+00:00
-- url     : https://prove2.me/theorems/4bdd7ab8-edb2-4f3e-adc3-43f47c931cbd
-- title:
--   Theorem 2.5.1 — coupling from the past is an exact sampler
-- statement:
--   **Theorem 2.5.1.** The backwards coalescence time $N^-$ is almost surely finite. In
--   addition, the random variable $Z = X^{-N^-}_0(i)$ has the distribution $\pi$.
--
--   **Exactly $\pi$** — not approximately, and not in the limit. That is what makes coupling from the
--   past an *exact sampling* algorithm and why Propp and Wilson's construction matters: a statement
--   that the law of $X_n$ converges to $\pi$ is a different and already classical result.
--
--   The proof is short. Since $P(N^- \le k) = P(N^+ \le k)$ for all $k$ (Property 2.5.2), the
--   finiteness of $N^-$ follows from that of the forwards coalescence time $N^+$ (Property 2.5.1).
--   And since $X^{-n}_0(i) = Z$ for $n \ge N^-$,
--   $$ P(Z = j) = \lim_{n\uparrow\infty} P(X^{-n}_0(i) = j) = \lim_{n\uparrow\infty} p_{ij}(n)
--   = \pi(j) , $$
--   the last equality by Kolmogorov's theorem for ergodic Markov chains.
--
--   $Z$ is characterised rather than constructed: the second clause says that **any** random variable
--   agreeing with the common value of the coalesced chains has law $\pi$, which is (2.5.10) without
--   an infimum. That the value does not depend on the starting state $i$ is supplied by the first
--   clause.
-- source:
--   Baccelli & Bremaud, Elements of Queueing Theory: Palm Martingale Calculus and Stochastic Recurrences, 2nd ed., Springer 2003, p. 112, Theorem 2.5.1

import Mathlib
import Definitions.Def_PalmQueueing_Recurrence_ExactSampling

/-!
# Theorem 2.5.1: the Propp-Wilson coupling-from-the-past theorem (§2.5.3, p.112)
-/

namespace PalmQueueing.Recurrence

open MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **Theorem 2.5.1** (p.112). The backwards coalescence time `N⁻` is almost surely finite. In
addition, the random variable `Z = X_0^{-N⁻}(i)` has the distribution `π`.

**Exactly `π`**, not approximately and not in the limit. That is what makes coupling from the past
an *exact sampling* algorithm and why Propp and Wilson's construction matters: a statement that
the law of `X_n` converges to `π` is a different and already classical result. The proof gets it
from `P(N⁻ ≤ k) = P(N⁺ ≤ k)` (Property 2.5.2), the a.s. finiteness of the forwards coalescence
time `N⁺` (Property 2.5.1), and the fact that `X_0^{-n}(i) = Z` for every `n ≥ N⁻`, so that
`P(Z = j) = lim_n P(X_0^{-n}(i) = j) = lim_n IPⁿ_{ij} = π(j)`.

`Z` is characterised rather than constructed: the second clause says that **any** random variable
agreeing with the common value of the coalesced chains has law `π`, which is (2.5.10) without an
inf. The value does not depend on `i`, which the first clause supplies. -/
theorem propp_wilson {r : ℕ} (C : CFTP Ω r) (i₀ : Fin r) :
    (∀ᵐ ω ∂C.P, ∃ n : ℕ, 1 ≤ n ∧ C.Coalesced n ω) ∧
    ∀ Z : Ω → Fin r, Measurable Z →
      (∀ᵐ ω ∂C.P, ∀ n : ℕ, 1 ≤ n → C.Coalesced n ω → Z ω = C.X (-(n : ℤ)) n i₀ ω) →
      ∀ j : Fin r, (C.P {ω | Z ω = j}).toReal = C.pi j := by sorry

end PalmQueueing.Recurrence
