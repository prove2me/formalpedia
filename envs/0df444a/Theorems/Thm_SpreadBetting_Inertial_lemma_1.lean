-- Prove2me | Theorems.Thm_SpreadBetting_Inertial_lemma_1
-- name    : SpreadBetting.Inertial.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T12:32:24.816232+00:00
-- url     : https://prove2.me/theorems/ed264dd7-f2f2-4753-9e7e-332cc611c231
-- title:
--   Lemma 1, p. 21 — range of the value function: 0 ≤ J̄¹(z) = J̄⁰(−z) < ∞
-- statement:
--   Let the market satisfy the standing assumptions, $\rho(z) = 1/(r_0 + rz)$ with $r \in (0, \bar r)$, and let $\bar J^1, \bar J^0$ be the functions (4.8). Then for all $z \in \mathbb Z$,
--   $$
--   0 \le \bar J^1(z) = \bar J^0(-z) < \infty,
--   $$
--   where finiteness means that the series $\sum_{n} \Lambda_n$ of (4.8)–(4.9) converges whenever $\bar z$ is finite.
--
--   $\bar J^i$ is the candidate value function of the informed bettor; this lemma makes it a well-defined nonnegative real.
--
--   **Formalization Note** The hypothesis $r \in (0, \bar r)$ is not printed in Lemma 1 but is in force in its proof (p. 51, "when $r \in (0,\bar r)$", using (LG.1-3) and (LG.2-3)). Because an infinite sum in Lean is $0$ when the series diverges, "$< \infty$" is stated as summability of $(\Lambda_n)$.
-- source:
--   Birge, Feng, Keskin & Schultz, SSRN 3283392 (version of April 14, 2020), p. 21, Lemma 1; (4.8)–(4.9) p. 20; proof p. 51

import Mathlib
import Definitions.Def_SpreadBetting_Inertial_Model

namespace SpreadBetting.Inertial

open MeasureTheory ProbabilityTheory Filter Topology

theorem lemma_1 (M : Market) (hM : M.Standing) (r : ℝ) (hr0 : 0 < r) (hr : r < rbar M) :
    let ρp := rhoIP M r
    (∀ z : ℤ, 0 ≤ Jbar1 M ρp z ∧ Jbar1 M ρp z = Jbar0 M ρp (-z)) ∧
    ((zbarSet M ρp).Nonempty → BddBelow (zbarSet M ρp) →
      Summable (Lam M ρp (zbar M ρp))) := by sorry

end SpreadBetting.Inertial
