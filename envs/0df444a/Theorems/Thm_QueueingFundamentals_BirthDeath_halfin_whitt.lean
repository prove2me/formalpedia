-- Prove2me | Theorems.Thm_QueueingFundamentals_BirthDeath_halfin_whitt
-- name    : QueueingFundamentals.BirthDeath.halfin_whitt
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-03T07:17:50.379081+00:00
-- url     : https://prove2.me/theorems/6eee4590-2c3b-4571-b30c-2657f1e008c4
-- title:
--   Theorem (Halfin and Whitt, 1981) — the square-root staffing law
-- statement:
--   Consider a sequence of $M/M/c$ queues indexed by $n = 1, 2, \dots$, where queue $n$ has $c_n = n$ servers and offered load $r_n$ with $0 < r_n < n$ (so that $\rho_n = r_n/n < 1$ and the Erlang-C formula $C(n, r_n)$ is defined). Let $\phi$ and $\Phi$ be the density and the distribution function of a standard normal random variable, and
--   $$\alpha(\beta) = \frac{\phi(\beta)}{\phi(\beta) + \beta\,\Phi(\beta)}.$$
--   Then
--   $$\lim_{n\to\infty} C(n, r_n) = \alpha, \quad 0 < \alpha < 1, \qquad \text{if and only if} \qquad \lim_{n\to\infty} \frac{n - r_n}{\sqrt n} = \beta, \quad \beta > 0,$$
--   where $\alpha$ and $\beta$ are related by $\alpha = \alpha(\beta)$. Precisely:
--
--   1. for every $\beta > 0$, $0 < \alpha(\beta) < 1$;
--   2. for every $\alpha \in (0, 1)$ there is exactly one $\beta > 0$ with $\alpha(\beta) = \alpha$;
--   3. for every $\beta > 0$, $(n - r_n)/\sqrt n \to \beta$ if and only if $C(n, r_n) \to \alpha(\beta)$.
--
--   The theorem justifies the square-root staffing rule $c \approx r + \beta\sqrt r$: the probability of delay stays at a fixed level strictly between $0$ and $1$ exactly when the number of servers in excess of the offered load grows like the square root of the offered load.
--
--   **Formalization Note** The book states the result without proof. The standing condition $\rho_n < 1$, under which the Erlang-C formula is defined (p.68), is the hypothesis $0 < r_n < n$ for $n \ge 1$; the term $n = 0$ of the sequence is irrelevant to the limits. Items 1–3 together are equivalent to the book's "if and only if, where $\alpha$ and $\beta$ are related via (2.44)".
-- source:
--   Gross, Shortle, Thompson & Harris, Fundamentals of Queueing Theory, 4th ed., Wiley 2008, DOI 10.1002/9781118625651, p.75, Theorem (Halfin and Whitt, 1981), §2.4, Eqs. (2.42)–(2.44)

import Mathlib
import Definitions.Def_QueueingFundamentals_BirthDeath_Erlang

namespace QueueingFundamentals.BirthDeath

open Filter Topology

/-- Theorem (Halfin and Whitt, 1981), §2.4, p.75. Consider a sequence of `M/M/c` queues indexed
by `n = 1, 2, …`, queue `n` having `c_n = n` servers and offered load `r_n` with `0 < r_n < n`.
Then `lim C(n, r_n) = α` with `0 < α < 1` if and only if `lim (n − r_n)/√n = β` with `β > 0`,
where `α` and `β` are related by (2.44), `α = φ(β)/(φ(β) + βΦ(β))`.

Stated as: (i) (2.44) sends every `β > 0` into `(0, 1)`; (ii) every `α ∈ (0, 1)` comes from exactly
one `β > 0`; (iii) for every `β > 0`, `(n − r_n)/√n → β` if and only if `C(n, r_n) → α(β)`. -/
theorem halfin_whitt (r : ℕ → ℝ) (hr : ∀ n : ℕ, 1 ≤ n → 0 < r n ∧ r n < n) :
    (∀ β : ℝ, 0 < β → 0 < halfinWhittAlpha β ∧ halfinWhittAlpha β < 1) ∧
      (∀ α : ℝ, 0 < α → α < 1 → ∃! β : ℝ, 0 < β ∧ halfinWhittAlpha β = α) ∧
      ∀ β : ℝ, 0 < β →
        (Tendsto (fun n : ℕ => erlangC n (r n)) atTop (𝓝 (halfinWhittAlpha β)) ↔
          Tendsto (fun n : ℕ => ((n : ℝ) - r n) / Real.sqrt n) atTop (𝓝 β)) := by sorry

end QueueingFundamentals.BirthDeath
