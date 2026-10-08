-- Prove2me | Theorems.Thm_SkutellaCQP_MaxCut_theorem_6_1
-- name    : SkutellaCQP.MaxCut.theorem_6_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T01:12:49.33407+00:00
-- url     : https://prove2.me/theorems/98f371cd-efdc-4ac7-85a3-437957e24590
-- title:
--   Theorem 6.1, p. 30 — for ρ ≤ 1, an m-cut of weight ≥ ρ·Z*_cut gives a schedule within ρ + m(1 − ρ) of optimal for Pm | | Σ wⱼCⱼ
-- statement:
--   Consider $n$ jobs with processing times $p_j>0$ and weights $w_j\ge0$ on $m\ge1$ identical parallel machines, Smith's order $\prec$, and the weighted complete graph $G_J$ with $c(jk)=w_jp_k$ for $k\prec j$. Let $\rho\le1$, and let $\sigma$ be an assignment of the jobs to the machines whose induced $m$-cut has weight at least $\rho$ times the weight of every $m$-cut of $G_J$, i.e. $c(E_{\mathrm{cut}}(\sigma))\ge\rho\cdot Z^*_{\mathrm{cut}}$. Then the schedule that uses $\sigma$ as its machine assignment and sequences each machine by $\prec$ satisfies
--   $$
--   \sum_j w_jC_j(\sigma)\le\big(\rho+m(1-\rho)\big)\sum_jw_jC_j(\tau)\qquad\text{for every assignment }\tau,
--   $$
--   that is, its value is at most $(\rho+m(1-\rho))\cdot Z^*$.
--
--   This is the paper's Theorem 6.1: a $\rho$-approximation algorithm for Max-$m$-Cut, applied to $G_J$, translates into an approximation algorithm for $Pm\,|\,|\sum w_jC_j$ with performance guarantee $\rho+m(1-\rho)$.
--
--   **Formalization Note** The algorithmic content ("translates into an approximation algorithm") is the map from cut to assignment, which is the identity on partitions; the running time is not formalized. "Weight at least $\rho\cdot Z^*_{\mathrm{cut}}$" is written as $\rho\,c(E_{\mathrm{cut}}(\tau))\le c(E_{\mathrm{cut}}(\sigma))$ for every assignment $\tau$, and $Z^*$ as the value of every assignment, so no maximum or minimum is a primitive.
-- source:
--   Skutella, Convex quadratic and semidefinite programming relaxations in scheduling, J. ACM 48 (2001), p. 30, Theorem 6.1 (proof on p. 31)

import Mathlib
import Definitions.Def_SkutellaCQP_MaxCut_Setting

namespace SkutellaCQP.MaxCut

open Finset

/-- Theorem 6.1, p. 30. Let `ρ ≤ 1`. If the assignment `σ` induces an `m`-cut of `G_J` whose weight
is at least `ρ` times the weight of every `m`-cut (i.e. at least `ρ · Z*_cut`), then the schedule
of `σ` has value at most `ρ + m(1 − ρ)` times the value of every schedule. -/
theorem theorem_6_1 {m n : ℕ} (p w : Fin n → ℝ) (hp : ∀ j, 0 < p j) (hw : ∀ j, 0 ≤ w j)
    (hm : 0 < m) (ρ : ℝ) (hρ : ρ ≤ 1) (σ : Fin n → Fin m)
    (hσ : ∀ τ : Fin n → Fin m, ρ * cut p w τ ≤ cut p w σ) :
    ∀ τ : Fin n → Fin m, val p w σ ≤ (ρ + m * (1 - ρ)) * val p w τ := by sorry

end SkutellaCQP.MaxCut
