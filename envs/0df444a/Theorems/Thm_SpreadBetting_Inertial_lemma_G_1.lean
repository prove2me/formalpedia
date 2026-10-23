-- Prove2me | Theorems.Thm_SpreadBetting_Inertial_lemma_G_1
-- name    : SpreadBetting.Inertial.lemma_G_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T12:32:15.670055+00:00
-- url     : https://prove2.me/theorems/b3da9daa-3408-4046-a149-49b341ecc88f
-- title:
--   Lemma G.1, p. 49 — ρ(z) = 1/(r₀ + rz) extended by (E.2): continuous strictly decreasing extension, ½ − α > ρ > 0, Σ Π (½ − ρ)/(½ + ρ) < ∞ for r < 4, inertia for r < r̄₀
-- statement:
--   Let the market satisfy the standing assumptions, let $r > 0$, and let $\rho$ be $\rho(z) = 1/(r_0 + rz)$ on $\mathbb Z_+$ extended to $\mathbb Z$ by (E.1) (this is (E.2)). Then:
--
--   1. (LG.1-1) The real extension (G.5), $\rho(x) = 1/(r_0 + rx)$ for $x \ge 0$ and $\rho(x) = \tfrac12 - F_1(F_0^{-1}(\tfrac12 + \tfrac1{r_0 - rx}))$ for $x < 0$, is continuous and strictly decreasing on $\mathbb R$, and twice differentiable on $\mathbb R \setminus \{0\}$.
--   2. (LG.1-2) For all $z \in \mathbb Z$, $\tfrac12 - \alpha = \rho(-\infty) > \rho(z) > \rho(\infty) = 0$.
--   3. (LG.1-3) If $r \in (0,4)$, then for every $z_0 \in \mathbb Z$,
--   $$
--   \sum_{n=0}^\infty \prod_{k=0}^n \frac{\tfrac12 - \rho(z_0+k)}{\tfrac12 + \rho(z_0+k)} < \infty.
--   $$
--   4. (LG.1-4) If $0 < r < \bar r_0$, then for every $z \in \mathbb Z$, $\rho(z+1)/\rho(z) > 1 - \tfrac{c}{2-c}$; hence (a) $\rho(z) - \rho(z+1) < \tfrac{c}{2-c}$ and (b) $\dfrac{\tfrac12 - \rho(z)}{\tfrac12 + \rho(z)} < \dfrac{(2-c)\rho(z+1) + c/2}{(2-c)\rho(z) + c/2}$.
--
--   Property (LG.1-4) is the "inertia" of the policy that removes the informed bettor's incentive to bluff.
--
--   **Formalization Note** $\rho(\pm\infty)$ are the limits along $z \to \pm\infty$ in $\mathbb Z$. "Twice differentiable at $x$" is stated as differentiability of $\rho$ and of its derivative at every $x \neq 0$. The hypothesis $r > 0$ is the policy's standing assumption (p. 15).
-- source:
--   Birge, Feng, Keskin & Schultz, SSRN 3283392 (version of April 14, 2020), p. 49, Lemma G.1, (G.5); (E.2) p. 45; (G.3) p. 49

import Mathlib
import Definitions.Def_SpreadBetting_Inertial_Model

namespace SpreadBetting.Inertial

open MeasureTheory ProbabilityTheory Filter Topology

theorem lemma_G_1 (M : Market) (hM : M.Standing) (r : ℝ) (hr : 0 < r) :
    let ρ := rhoExt M (rhoIP M r)
    -- (LG.1-1)
    (Continuous (rhoReal M r) ∧ StrictAnti (rhoReal M r) ∧
      ∀ x : ℝ, x ≠ 0 → DifferentiableAt ℝ (rhoReal M r) x ∧
        DifferentiableAt ℝ (deriv (rhoReal M r)) x) ∧
    -- (LG.1-2)
    (∀ z : ℤ, 0 < ρ z ∧ ρ z < 1 / 2 - alpha M) ∧
    Tendsto ρ atBot (𝓝 (1 / 2 - alpha M)) ∧ Tendsto ρ atTop (𝓝 0) ∧
    -- (LG.1-3)
    (r < 4 → ∀ z0 : ℤ, Summable (fun n : ℕ => ∏ k ∈ Finset.range (n + 1),
      (1 / 2 - ρ (z0 + k)) / (1 / 2 + ρ (z0 + k)))) ∧
    -- (LG.1-4)
    (r < rbar0 M → ∀ z : ℤ, 1 - M.c / (2 - M.c) < ρ (z + 1) / ρ z ∧
      ρ z - ρ (z + 1) < M.c / (2 - M.c) ∧
      (1 / 2 - ρ z) / (1 / 2 + ρ z)
        < ((2 - M.c) * ρ (z + 1) + M.c / 2) / ((2 - M.c) * ρ z + M.c / 2)) := by sorry

end SpreadBetting.Inertial
