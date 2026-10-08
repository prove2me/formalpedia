-- Prove2me | Theorems.Thm_PalmQueueing_Loynes_loynes_stability
-- name    : PalmQueueing.Loynes.loynes_stability
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-01T23:53:07.604096+00:00
-- url     : https://prove2.me/theorems/9d36f227-19d4-4971-b01b-4070cf0fd403
-- title:
--   Theorem 2.1.1 — the Loynes stability theorem
-- statement:
--   **Theorem 2.1.1 (Loynes).** "The fundamental result of stability." Under the stability
--   condition
--   $$ \rho < 1 , \tag{2.1.11} $$
--   there exists a unique finite workload process $\{W(t)\}$, $t \in \mathbb{R}$, compatible with the
--   flow $\{\theta_t\}$, and satisfying equation (2.1.6) for all $t \in \mathbb{R}$. This process is
--   such that
--   $$ W(0) = \sup_{n \le 0} \Big( T_n + \sum_{i=n}^{0} \sigma_i \Big)^+ . \tag{2.1.12} $$
--   Moreover, there are an infinite number of negative indices $n$ and an infinite number of positive
--   indices $n$ such that
--   $$ W(T_n-) = 0 . \tag{2.1.13} $$
--   If the traffic intensity $\rho$ is strictly larger than $1$, there exists no finite
--   $P$-stationary workload process $\{W(t)\}$, $t \in \mathbb{R}$.
--
--   All four clauses are in the statement because each is load-bearing. Existence alone is not the
--   theorem: the explicit supremum is what "the Loynes construction" *means*, uniqueness is what makes
--   the stationary regime *the* stationary regime, and the $\rho > 1$ half is what turns $\rho < 1$
--   from a sufficient condition into a criterion. Uniqueness is among the
--   $\theta_t$-**compatible** workload processes, not among all of them; without compatibility it is
--   false. Boundedness above of the Loynes set is part of the conclusion rather than a hypothesis,
--   since a supremum of an unbounded set of reals would otherwise default to $0$ and let the zero
--   process satisfy (2.1.12).
--
--   The reading of (2.1.12): looking back from the origin, the work brought by customers $n, \dots, 0$
--   is $\sum_{i=n}^{0}\sigma_i$ and the time since elapsed is $-T_n$, so each term is what would still
--   be in the system at time $0$ had the queue been empty just before customer $n$; the workload is
--   the largest of these over how far back one looks.
--
--   The critical case is deliberately **not** part of the statement. p.80 says that when $\rho = 1$
--   there "may or may not" exist a finite $P$-stationary workload process compatible with the flow.
--   That is an open dichotomy, not a result, and asserting it either way would misreport the book.
--
--   **Formalization Note.** $\rho = \lambda E^0_A[\sigma_0]$ takes values in $[0,\infty]$ (`Queue.trafficIntensity`), so a service time with $E^0_A[\sigma_0] = \infty$ gives $\rho = \infty$ and falls under the non-existence half. Every pathwise clause — Lindley's equation (2.1.6) with right-continuity and left limits, formula (2.1.12), and (2.1.13) — holds $P$-almost surely (`IsWorkloadPath` at $P$-almost every $\omega$), as for any identity between random variables: on a $P$-null invariant set of sample paths no finite workload need exist. The unique process is a random process ($W(t)$ measurable for each $t$), and uniqueness is among measurable, $\theta_t$-compatible processes satisfying (2.1.6) $P$-a.s., with equality $P$-a.s. for all $t$ simultaneously.
-- source:
--   Baccelli & Bremaud, Elements of Queueing Theory: Palm Martingale Calculus and Stochastic Recurrences, 2nd ed., Springer 2003, p. 80, Theorem 2.1.1

import Mathlib
import Definitions.Def_PalmQueueing_Palm_PointProcess
import Definitions.Def_PalmQueueing_Loynes_SingleServerQueue
import Definitions.Def_PalmQueueing_Loynes_StationaryRegime

/-!
# Theorem 2.1.1: the Loynes stability theorem (§2.1.2, p.80)
-/

namespace PalmQueueing.Loynes

open MeasureTheory Filter Topology
open PalmQueueing.Palm

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **The Loynes stability theorem**, Theorem 2.1.1 (p.80), "the fundamental result of stability".

Under the stability condition `(2.1.11) ρ < 1` there exists a **unique** finite workload process
`{W(t)}, t ∈ ℝ`, compatible with the flow `{θ_t}` and satisfying Lindley's equation `(2.1.6)` for
all `t ∈ ℝ`. This process is such that

`(2.1.12)  W(0) = sup_{n ≤ 0} ( T_n + Σ_{i=n}^{0} σ_i )⁺`,

and there are an infinite number of negative indices `n` and an infinite number of positive indices
`n` such that `(2.1.13) W(T_n−) = 0`. If `ρ > 1` there exists **no** finite `P`-stationary workload
process.

All four clauses are in the statement, because each is load-bearing. Existence alone is not the
theorem: the explicit supremum is what "the Loynes construction" means, uniqueness is what makes
the stationary regime *the* stationary regime, and the `ρ > 1` half is what turns `ρ < 1` from a
sufficient condition into a criterion. `BddAbove` on the Loynes set is part of the conclusion and
not a hypothesis — without it a `sSup` of an unbounded set would default to `0` and the identity
could be satisfied by the zero process.

Uniqueness is among the `θ_t`-**compatible** workload processes, not among all of them; dropping
compatibility makes it false. It is also among **random** processes (each `W'(t)` measurable): on
every typical sample path Lindley's equation has other whole-line solutions "coming down from
`+∞`", and a non-measurable choice of one of them per `θ_t`-orbit would be compatible.

Every pathwise clause holds `P`-a.s., which is how the book's random-variable identities are meant:
on a `P`-null `θ_t`-invariant set of sample paths where `Σ σ_i` outruns `−T_n` no finite workload
exists at all, so an "for every `ω`" existence claim would be false. For the same reason the
workload equation (2.1.6) is required `P`-a.s. (`IsWorkloadPath`), in the hypotheses as in the
conclusion.

`ρ` is `Queue.trafficIntensity`, valued in `[0, ∞]`: when `E⁰_A[σ₀] = ∞` it is `+∞` and the
non-existence half applies, whereas a Bochner integral would have set it to `0`.

The critical case `ρ = 1` is deliberately absent. p.80 says that there "may or may not" exist a
finite `P`-stationary workload process, which is an open dichotomy and not a result; stating it
either way would misreport the book. -/
theorem loynes_stability (Q : Queue Ω) :
    (Q.trafficIntensity < 1 →
      ∃ W Wl : ℝ → Ω → ℝ,
        (∀ t : ℝ, Measurable (W t)) ∧ IsCompatible Q.toPalmSetting.θ W ∧
        (∀ᵐ ω ∂Q.toPalmSetting.P, IsWorkloadPath Q W Wl ω) ∧
        (∀ W' Wl' : ℝ → Ω → ℝ, (∀ t : ℝ, Measurable (W' t)) →
          IsCompatible Q.toPalmSetting.θ W' →
          (∀ᵐ ω ∂Q.toPalmSetting.P, IsWorkloadPath Q W' Wl' ω) →
          ∀ᵐ ω ∂Q.toPalmSetting.P, ∀ t : ℝ, W' t ω = W t ω) ∧
        (∀ᵐ ω ∂Q.toPalmSetting.P, BddAbove (loynesSet Q ω) ∧ W 0 ω = sSup (loynesSet Q ω)) ∧
        (∀ᵐ ω ∂Q.toPalmSetting.P,
          {n : ℤ | n < 0 ∧ Wl (Q.toPalmSetting.N.T n ω) ω = 0}.Infinite ∧
          {n : ℤ | 0 < n ∧ Wl (Q.toPalmSetting.N.T n ω) ω = 0}.Infinite)) ∧
    (1 < Q.trafficIntensity →
      ¬ ∃ W Wl : ℝ → Ω → ℝ, IsCompatible Q.toPalmSetting.θ W ∧
        ∀ᵐ ω ∂Q.toPalmSetting.P, IsWorkloadPath Q W Wl ω) := by sorry

end PalmQueueing.Loynes
