-- Prove2me | Theorems.Thm_SolodovSvaiterVI_Alg21_eq2_6_fejer_step
-- name    : SolodovSvaiterVI.Alg21.eq2_6_fejer_step
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-29T10:34:32.632627+00:00
-- url     : https://prove2.me/theorems/2ba4c6f2-4abd-4bf3-9390-4268f65b7d12
-- title:
--   Eq. (2.6): Fejér-type decrease of the distance to every solution in one step
-- statement:
--   Let $C$ be a closed convex subset of $\mathbb{R}^n$ and $F : \mathbb{R}^n \to \mathbb{R}^n$ continuous. Assume the solution set $S$ of $\mathrm{VI}(F, C)$ is nonempty and condition (1.2) holds, and let $\gamma, \sigma \in (0,1)$. Let $x \in C$ with $r(x) \ne 0$, let $k$ be a nonnegative integer satisfying (2.1) at $x$, and put
--
--   $$z = x - \gamma^k r(x),\quad H = \{y \mid \langle F(z), y - z\rangle \le 0\},\quad \bar x = P_H[x],\quad x^+ = P_{C \cap H}[x].$$
--
--   Then for every solution $x^* \in S$,
--
--   $$\|x^+ - x^*\|^2 \le \|x - x^*\|^2 - \|x^+ - \bar x\|^2 - \left(\frac{\gamma^k \sigma}{\|F(z)\|}\right)^2 \|r(x)\|^4. \tag{2.6}$$
--
--   Along a run of Algorithm 2.1 ($x = x^i$, $\gamma^k = \eta_i$, $x^+ = x^{i+1}$), (2.6) shows that the distance of the iterates to every solution is nonincreasing, with a quantified decrease; this is the backbone of the convergence proof.
--
--   **Formalization Note** Single-step form: the paper writes (2.6) along the run with $x^i$ and $\eta_i = \gamma^{k_i}$; here $x$ and $k$ are generic, with $k$ satisfying (2.1) at $x$. Under the hypotheses $F(z) \ne 0$, so the division is genuine (Lean's convention $a/0 = 0$ is never invoked). Projections are `projOnto`.
-- source:
--   Solodov & Svaiter, A New Projection Method for Variational Inequality Problems, SIAM J. Control Optim. 37 (1999), pp. 769–770, proof of Theorem 2.1, Eq. (2.6)

import Mathlib
import Definitions.Def_SolodovSvaiterVI_Alg21_projOnto
import Definitions.Def_SolodovSvaiterVI_Alg21_viSol
import Definitions.Def_SolodovSvaiterVI_Alg21_SatisfiesCond12
import Definitions.Def_SolodovSvaiterVI_Alg21_residual
import Definitions.Def_SolodovSvaiterVI_Alg21_halfspace
import Definitions.Def_SolodovSvaiterVI_Alg21_ArmijoHolds

namespace SolodovSvaiterVI.Alg21

/-- Solodov–Svaiter, proof of Theorem 2.1, (2.6) (pp. 769–770), for one step of Algorithm 2.1:
with `z = x − γᵏ r(x)`, `H = {y | ⟨F(z), y − z⟩ ≤ 0}`, `x̄ = P_H[x]` and `x⁺ = P_{C∩H}[x]`,
for every solution `x*`,
`‖x⁺ − x*‖² ≤ ‖x − x*‖² − ‖x⁺ − x̄‖² − (γᵏ σ / ‖F(z)‖)² ‖r(x)‖⁴`.

**Formalization Note.** Single-step form: the paper writes (2.6) along the run, with `xⁱ`,
`ηᵢ = γ^{kᵢ}`; here `x` and `k` are generic, with `k` satisfying (2.1) at `x`. -/
theorem eq2_6_fejer_step {n : ℕ}
    (F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (C : Set (EuclideanSpace ℝ (Fin n))) (hCc : IsClosed C) (hCcv : Convex ℝ C)
    (hF : Continuous F) (hS : (viSol F C).Nonempty) (h12 : SatisfiesCond12 F C)
    (gamma sigma : ℝ) (hγ0 : 0 < gamma) (hγ1 : gamma < 1) (hσ0 : 0 < sigma) (hσ1 : sigma < 1)
    (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ C) (hr : residual F C x ≠ 0)
    (k : ℕ) (hk : ArmijoHolds F C gamma sigma x k) :
    let z := x - gamma ^ k • residual F C x
    let H := halfspace (F z) z
    let xbar := projOnto H x
    let xnext := projOnto (C ∩ H) x
    ∀ xs ∈ viSol F C,
      ‖xnext - xs‖ ^ 2 ≤
        ‖x - xs‖ ^ 2 - ‖xnext - xbar‖ ^ 2 -
          (gamma ^ k * sigma / ‖F z‖) ^ 2 * ‖residual F C x‖ ^ 4 := by sorry

end SolodovSvaiterVI.Alg21
