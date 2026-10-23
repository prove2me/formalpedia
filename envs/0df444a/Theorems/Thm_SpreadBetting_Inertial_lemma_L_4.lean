-- Prove2me | Theorems.Thm_SpreadBetting_Inertial_lemma_L_4
-- name    : SpreadBetting.Inertial.lemma_L_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T12:33:02.475726+00:00
-- url     : https://prove2.me/theorems/dff1c490-f041-4530-8d53-ddf397d647f8
-- title:
--   Lemma L.4, p. 71 — for slowly vanishing regular ρ and finite Z̄, (1/(4 − 2c)) Σ_t Ẽ^z_1 l̃(Z_t) = Ẽ^z_1 v(Z_{T+1}) − v(z) with v of (L.7) increasing and v(z) = O(Σ_{k≤z} ρ(k))
-- statement:
--   Let the market satisfy the standing assumptions, let $\rho : \mathbb Z_+ \to (0,\tfrac12-\alpha)$ be slowly vanishing and regular, extended to $\mathbb Z$ by (E.1), and let $\bar Z \in \mathbb Z$. Under $H_1$ let the informed bettor use the $\bar Z$-threshold strategy, write $\tilde{\mathbb E}_1^z$ for expectations from $Z_1 = z$, and $\tilde l(z) = (2-c)\rho(z)\mathbb I\{z < \bar Z\} + (4-2c)\rho^2(z)\mathbb I\{z \ge \bar Z\}$. Define $v(\bar Z - 1) = 0$ and, for $z \ge \bar Z$,
--   $$
--   v(z) = \Big(1 + \sum_{n=\bar Z}^{z-1}\prod_{m=\bar Z}^n q(m)\Big)\frac{\rho(\bar Z-1)}{2} + \sum_{n=\bar Z}^{z-1}\sum_{k=\bar Z}^n \frac{\rho^2(k)}{\tfrac12 - \rho(k)}\prod_{m=k}^n q(m),\qquad q(m) = \frac{\tfrac12-\rho(m)}{\tfrac12+\rho(m)}. \tag{L.7}
--   $$
--   Then:
--   1. For all $z \ge \bar Z - 1$ and $T \in \mathbb Z_+$,
--   $$
--   \frac{1}{4-2c}\sum_{t=1}^T \tilde{\mathbb E}_1^z\,\tilde l(Z_t) = \tilde{\mathbb E}_1^z\, v(Z_{T+1}) - v(z). \tag{L.6}
--   $$
--   2. $v$ is strictly increasing on $\{\bar Z - 1, \bar Z, \dots\}$.
--   3. $v(z) \to \infty$ as $z \to \infty$, and $v(z) = O\big(\sum_{k=1}^z \rho(k)\big)$.
--
--   **Formalization Note** "Increasing" is read as strictly increasing, the paper's usage (cf. Lemma L.2). The growth clause is stated along $z \in \mathbb N$; $O(\cdot)$ is Definition 1.
-- source:
--   Birge, Feng, Keskin & Schultz, SSRN 3283392 (version of April 14, 2020), p. 71, Lemma L.4, (L.4), (L.6)–(L.7)

import Mathlib
import Definitions.Def_SpreadBetting_Inertial_Model
import Definitions.Def_SpreadBetting_Inertial_Chain

namespace SpreadBetting.Inertial

open MeasureTheory ProbabilityTheory Filter Topology

theorem lemma_L_4 (M : Market) (hM : M.Standing) (ρp : ℕ → ℝ) (hsv : SlowlyVanishing M ρp)
    (hreg : Regular ρp) (Zb : ℤ) :
    let ρ := rhoExt M ρp
    let q : ℤ → ℝ := fun m => (1 / 2 - ρ m) / (1 / 2 + ρ m)
    let v : ℤ → ℝ := fun z =>
      if z = Zb - 1 then 0
      else (1 + ∑ n ∈ Finset.Icc Zb (z - 1), ∏ m ∈ Finset.Icc Zb n, q m) * (ρ (Zb - 1) / 2)
        + ∑ n ∈ Finset.Icc Zb (z - 1), ∑ k ∈ Finset.Icc Zb n,
            (ρ k ^ 2 / (1 / 2 - ρ k)) * ∏ m ∈ Finset.Icc k n, q m
    let ξ := threshStrat 1 (fun z => z < Zb)
    -- (L.6)
    (∀ z : ℤ, Zb - 1 ≤ z → ∀ T : ℕ, 1 ≤ T →
      (1 / (4 - 2 * M.c)) * cumExp M ρp 1 ξ (fun z _ _ => lossFn M ρp (fun z => z < Zb) z) T [] z
        = termExp M ρp 1 ξ v T [] z - v z) ∧
    StrictMonoOn v {z : ℤ | Zb - 1 ≤ z} ∧
    Tendsto (fun n : ℕ => v n) atTop atTop ∧
    IsBigOP (fun n : ℕ => v n) (fun n : ℕ => ∑ k ∈ Finset.Icc 1 n, ρp k) := by sorry

end SpreadBetting.Inertial
