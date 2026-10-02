-- Prove2me | Theorems.Thm_SennottDP_Fatou_liminf_min_comm
-- name    : SennottDP.Fatou.liminf_min_comm
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-01T11:32:23.076703+00:00
-- url     : https://prove2.me/theorems/8f8e1c79-7d6c-4c4e-91e0-eecb9d1ef933
-- title:
--   Proposition A.1.3 — lim inf commutes with a minimum over a finite set
-- statement:
--   Let $A$ be a finite nonempty set and, for each $a\in A$, let $(u(a,N))_{N}$ be a sequence of extended real numbers in $[-\infty,\infty]$.
--
--   1. The limit inferior may be passed through the minimum:
--   $$\liminf_{N\to\infty}\ \min_{a\in A} u(a,N) \;=\; \min_{a\in A}\ \liminf_{N\to\infty} u(a,N).$$
--   2. If $\lim_{N\to\infty} u(a,N)$ exists (possibly $\pm\infty$) for every $a\in A$, then
--   $$\lim_{N\to\infty}\ \min_{a\in A} u(a,N) \;=\; \min_{a\in A}\ \lim_{N\to\infty} u(a,N).$$
--
--   Part 1 fails with the minimum replaced by a maximum (Example A.1.4). In dynamic programming this is what lets a limit inferior be moved inside the minimization over the finite action set of an optimality equation.
--
--   **Formalization Note** The minimum over the finite nonempty type `A` is written `⨅ a`; limits and lower limits are taken in `EReal` along `atTop`.
-- source:
--   Sennott, Stochastic Dynamic Programming and the Control of Queueing Systems (Wiley, 1999), p. 271, Proposition A.1.3

import Mathlib

open Filter Topology
open scoped ENNReal

namespace SennottDP.Fatou

/-- Sennott (1999), Proposition A.1.3, p. 271. `A` is a finite nonempty set and `u(a, N)` is
extended-real valued; the minimum over `A` is `⨅ a` (a minimum, since `A` is finite and
nonempty). (i) `liminf_N min_a u(a, N) = min_a liminf_N u(a, N)`; (ii) if `lim_N u(a, N) = l(a)`
exists (in `[−∞, ∞]`) for every `a`, then `lim_N min_a u(a, N) = min_a l(a)`. -/
theorem liminf_min_comm {A : Type*} [Fintype A] [Nonempty A] (u : A → ℕ → EReal) :
    liminf (fun N => ⨅ a, u a N) atTop = ⨅ a, liminf (fun N => u a N) atTop ∧
    ∀ l : A → EReal, (∀ a, Tendsto (fun N => u a N) atTop (𝓝 (l a))) →
      Tendsto (fun N => ⨅ a, u a N) atTop (𝓝 (⨅ a, l a)) := by sorry

end SennottDP.Fatou
