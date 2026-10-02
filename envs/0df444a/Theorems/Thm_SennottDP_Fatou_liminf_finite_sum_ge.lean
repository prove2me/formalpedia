-- Prove2me | Theorems.Thm_SennottDP_Fatou_liminf_finite_sum_ge
-- name    : SennottDP.Fatou.liminf_finite_sum_ge
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-01T11:38:55.107144+00:00
-- url     : https://prove2.me/theorems/dd8dd4c4-5ac7-4766-9f3b-533a22c4f686
-- title:
--   Proposition A.1.5 — lim inf of a finite sum dominates the sum of the lim infs
-- statement:
--   Let $G$ be a finite nonempty set and, for each $j\in G$, let $(u(j,N))_N$ be a sequence with values in $(-\infty,\infty]$. Assume there is no indeterminate form in the sum on the right below, that is, it is not the case that $\liminf_N u(j,N)=-\infty$ for some $j\in G$ while $\liminf_N u(k,N)=+\infty$ for some $k\in G$. Then
--   $$\liminf_{N\to\infty}\ \sum_{j\in G} u(j,N) \;\ge\; \sum_{j\in G}\ \liminf_{N\to\infty} u(j,N). \tag{A.2}$$
--
--   The sum on the left never has an indeterminate form because no $u(j,N)$ equals $-\infty$. The inequality may be strict (Example A.1.6). It is the finite-set step from which the countable Fatou-type results of the appendix are built.
--
--   **Formalization Note** Values are in `EReal`; the hypothesis `u j N ≠ ⊥` encodes $(-\infty,\infty]$, and the no-indeterminate-form condition is stated explicitly, so Lean's convention $-\infty+\infty=-\infty$ in `EReal` is never used on the right.
-- source:
--   Sennott, Stochastic Dynamic Programming and the Control of Queueing Systems (Wiley, 1999), p. 272, Proposition A.1.5, Eq. (A.2)

import Mathlib

open Filter Topology
open scoped ENNReal

namespace SennottDP.Fatou

/-- Sennott (1999), Proposition A.1.5, p. 272, (A.2). `G` is a finite nonempty set and
`u(j, N) ∈ (−∞, ∞]`. Under the condition that there is no indeterminate form in the sum on the
right (no `j` with `liminf_N u(j, N) = −∞` together with a `k` with `liminf_N u(k, N) = +∞`),
`liminf_N ∑_{j ∈ G} u(j, N) ≥ ∑_{j ∈ G} liminf_N u(j, N)`. -/
theorem liminf_finite_sum_ge {G : Type*} [Fintype G] [Nonempty G] (u : G → ℕ → EReal)
    (hu : ∀ j N, u j N ≠ ⊥)
    (hind : ¬ ((∃ j, liminf (fun N => u j N) atTop = ⊥) ∧
      (∃ k, liminf (fun N => u k N) atTop = ⊤))) :
    ∑ j, liminf (fun N => u j N) atTop ≤ liminf (fun N => ∑ j, u j N) atTop := by sorry

end SennottDP.Fatou
