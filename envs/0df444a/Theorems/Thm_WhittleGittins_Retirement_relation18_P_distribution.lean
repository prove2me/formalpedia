-- Prove2me | Theorems.Thm_WhittleGittins_Retirement_relation18_P_distribution
-- name    : WhittleGittins.Retirement.relation18_P_distribution
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:55:35.988564+00:00
-- url     : https://prove2.me/theorems/897d67d9-9a06-4678-ba28-3735c927d471
-- title:
--   Relation (18) — Pᵢ(x, s, M) = ∏_{j≠i} ∂φⱼ/∂M is a distribution function in M, equal to 1 for M ≥ M₍ᵢ₎
-- statement:
--   In Whittle's bandit process with per-project horizons $s = (s_1,\dots,s_N)$, let $\varphi_j(x_j, s_j, M)$ be the value of the single-project $M$-process for project $j$ (14), let $M_j = M_j(x_j, s_j)$ be its index, the infimal $M$ with $\varphi_j(x_j, s_j, M) = M$, and define
--   $$P_i(x, s, M) = \prod_{j\ne i} \frac{\partial \varphi_j(x_j, s_j, M)}{\partial M}. \qquad (17)$$
--   Regarded as a function of $M$, $P_i$ is non-negative, non-decreasing and at most $1$, and
--   $$P_i(x, s, M) = 1 \quad\text{for}\quad M \ge M_{(i)} \triangleq \max_{j\ne i} M_j, \qquad (18)$$
--   the maximum being over the other projects that can still be operated ($s_j > 0$). Moreover each such index satisfies $M_j \le K$. Hence $P_i(x, s, \cdot)$ is a distribution function in $M$ with all its support in $M \le M_{(i)} \le K$.
--
--   This is the step of the proof of Theorem 1 that allows $\hat F$ of (13) to be integrated by parts against $P_i$.
--
--   **Formalization Note** $\partial/\partial M$ is the right derivative. Projects $j$ with $s_j = 0$ have $\varphi_j(x_j, 0, M) = M$, derivative $1$ and index $-\infty$; they are excluded from the maximum defining $M_{(i)}$ (if no other project is active, $M_{(i)} = -\infty$ and $P_i \equiv 1$). Projects are indexed by `Fin N`.
-- source:
--   Whittle, Multi-armed Bandits and the Gittins Index, J. R. Statist. Soc. B 42 (1980), p. 147 (PDF 5), Section 4, relations (17) and (18)

import Mathlib
import Definitions.Def_WhittleGittins_Retirement_BanditProcess

namespace WhittleGittins.Retirement

open MeasureTheory ProbabilityTheory

/-- Relation (18) (p. 147): `Pᵢ(x, s, M) = ∏_{j≠i} ∂φⱼ(xⱼ, sⱼ, M)/∂M` is, as a function of `M`,
non-negative, non-decreasing, at most one, and equal to one for `M ≥ M₍ᵢ₎ = max_{j≠i} Mⱼ` (the
maximum over the other active projects); moreover every index of an active project is `≤ K`. -/
theorem relation18_P_distribution {N : ℕ} {X : Fin N → Type*} [∀ i, MeasurableSpace (X i)]
    (B : BanditProcess N X) (x : ∀ j, X j) (s : Fin N → ℕ) (i : Fin N) :
    (∀ M, 0 ≤ Pdist B x s i M) ∧ Monotone (Pdist B x s i) ∧ (∀ M, Pdist B x s i M ≤ 1) ∧
      (∀ M, (∀ j, j ≠ i → 0 < s j → index B j (x j) (s j) ≤ M) → Pdist B x s i M = 1) ∧
      (∀ j, 0 < s j → index B j (x j) (s j) ≤ B.K) := by sorry

end WhittleGittins.Retirement
