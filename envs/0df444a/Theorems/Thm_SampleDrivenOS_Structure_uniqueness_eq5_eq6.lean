-- Prove2me | Theorems.Thm_SampleDrivenOS_Structure_uniqueness_eq5_eq6
-- name    : SampleDrivenOS.Structure.uniqueness_eq5_eq6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T04:32:31.880251+00:00
-- url     : https://prove2.me/theorems/f57935f6-f3d2-418a-a9d4-fa7a868a6880
-- title:
--   Proof of Theorem 2, p. 10 — for given thresholds, equations (5) and (6) have a unique solution
-- statement:
--   Let $0\le p<1$ and let $(t_i)_{i\ge0}$ be a non-decreasing sequence in $[p,1]$ with $t_0=p$. Suppose $q_1$ and $q_2$ are feasible for CLP$_p$ and both satisfy equations (5) and (6): for $m\in\{1,2\}$, every $\ell\ge1$ and every $\tau\in[p,1)$,
--   $$\tau\,q_m(\tau,\ell)+\int_p^\tau\sum_{s\ge1}q_m(\sigma,s)\,d\sigma=1\ \text{ if }\tau\ge t_\ell,\qquad q_m(\tau,\ell)=0\ \text{ if }\tau<t_\ell .$$
--   Then $q_1(\tau,\ell)=q_2(\tau,\ell)$ for all $\tau\in[p,1)$ and $\ell\ge1$.
--
--   This is the uniqueness half of the second part of the proof of Theorem 2: once the thresholds are fixed, (5)–(6) determine the solution, so it suffices to exhibit one solution, (7).
--
--   **Formalization Note** Solutions are taken among feasible functions (nonnegative, integrable components, constraint of CLP$_p$). Equations (5)–(6) are imposed on $[p,1)$ (see Theorem 2). Existence is not part of this statement.
-- source:
--   Correa, Cristi, Epstein & Soto, Sample-Driven Optimal Stopping: From the Secretary Problem to the i.i.d. Prophet Inequality, arXiv:2011.06516v2, p. 10 (PDF p. 11), proof of Theorem 2, uniqueness of the solution of (5)–(6)

import Mathlib
import Definitions.Def_SampleDrivenOS_Structure_Setting

open MeasureTheory Set

namespace SampleDrivenOS.Structure

theorem uniqueness_eq5_eq6 (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p < 1) (t : ℕ → ℝ)
    (ht : Monotone t) (ht0 : t 0 = p) (htI : ∀ i : ℕ, t i ∈ Icc p 1)
    (q₁ q₂ : ℝ → ℕ → ℝ) (hq₁ : IsFeasible p q₁) (hq₂ : IsFeasible p q₂)
    (h₁ : SolvesEq5Eq6 p t q₁) (h₂ : SolvesEq5Eq6 p t q₂) :
    ∀ τ ∈ Ico p 1, ∀ ℓ : ℕ, 1 ≤ ℓ → q₁ τ ℓ = q₂ τ ℓ := by sorry

end SampleDrivenOS.Structure
