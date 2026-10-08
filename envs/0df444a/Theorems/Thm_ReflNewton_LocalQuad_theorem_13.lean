-- Prove2me | Theorems.Thm_ReflNewton_LocalQuad_theorem_13
-- name    : ReflNewton.LocalQuad.theorem_13
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T16:57:42.625576+00:00
-- url     : https://prove2.me/theorems/827646ea-4034-47e0-a5a5-fe2f4493451c
-- title:
--   Theorem 13: local quadratic convergence of the interior-reflective Newton method
-- statement:
--   Let $x_*$ be a nondegenerate feasible point satisfying $D(x_*)^2g(x_*)=0$ and positive definiteness of the Hessian on its free coordinates. Suppose $f$ is twice continuously differentiable on an open set containing the box, and its Hessian is locally Lipschitz at $x_*$. Fix the nonnegative constant $\chi_\alpha$ in the step-size rule $|\alpha_k-1|\le\chi_\alpha\|D(x_k)^2g(x_k)\|$. Then there are a radius $r>0$ and a constant $C$, independent of the run, such that every local interior-reflective Newton run with $x_1\in\operatorname{int}(\mathcal F)\cap B(x_*,r)$ remains strictly interior and satisfies
--
--   $$
--   \|x_{k+1}-x_*\|\le C\|x_k-x_*\|^2\quad\text{for every }k,
--   \qquad x_k\longrightarrow x_*.
--   $$
--
--   This is the local rate claim for the feasible reflective method of Fig. 11.
--
--   **Formalization Note** The printed Theorem 13 assumes only $C^2$ smoothness. A local Lipschitz Hessian is necessary for its quadratic claim: with no bounds and $f(x)=x^2/2+(2/5)|x|^{5/2}$, the assumptions on page 213 hold but ordinary Newton iteration is only order $3/2$. The added hypothesis supplies Theorem 11's Jacobian estimate (6.5). Second, Fig. 11 prints the step-size rule as $|\alpha_k-1|=O(\|D_kg_k\|)$, and the proof asserts $\|D_kg_k\|=O(\|x_k-x_*\|)$; that fails at active bounds, where $D_kg_k$ is of order $\|x_k-x_*\|^{1/2}$. On $[0,\infty)$ with $f(x)=x$ and $x_*=0$ the Newton step is $-x$, and $\alpha_k=1-\chi_\alpha\sqrt{x_k}$ obeys the printed rule but gives $x_{k+1}=\chi_\alpha x_k^{3/2}$. The run therefore bounds $|\alpha_k-1|$ by $\chi_\alpha\|D(x_k)^2g(x_k)\|$, which is $O(\|x_k-x_*\|)$ as the proof requires. The paper's global level-set compactness assumption is omitted because this is a local statement. The sequence starts at Lean index zero for the paper's $x_1$.
-- source:
--   Coleman & Li, On the convergence of interior-reflective Newton methods for nonlinear minimization subject to bounds, Math. Programming 67 (1994), p. 213, Theorem 13; proof pp. 213–214; added hypothesis motivated by Theorem 11 (6.5), p. 211

import Mathlib
import Definitions.Def_LewisTorczon_BoundPS_Box
import Definitions.Def_ReflNewton_LocalQuad_Setting

namespace ReflNewton.LocalQuad

/-- Theorem 13, with the local Lipschitz-Hessian hypothesis needed for its claimed quadratic rate,
for runs of `IsLocalNewtonRun` (Fig. 11 with the step-size rule corrected to `|α_k − 1| ≤ χα ‖D_k² g_k‖`). -/
theorem theorem_13 {n : ℕ} (l u : Fin n → EReal)
    (hl : ∀ i, l i ≠ ⊤) (hu : ∀ i, u i ≠ ⊥) (hlu : l ≤ u)
    (f : ReflNewton.FirstOrder.E n → ℝ) (D : Set (ReflNewton.FirstOrder.E n)) (hDo : IsOpen D)
    (hFD : LewisTorczon.BoundPS.box l u ⊆ D) (hf : ContDiffOn ℝ 2 f D)
    (xstar : ReflNewton.FirstOrder.E n) (hnd : IsNondegenerate l u f xstar)
    (hsos : SecondOrderSufficient l u f xstar)
    (hLip : ∃ κ r₀ : ℝ, 0 < r₀ ∧
      ∀ x ∈ Metric.ball xstar r₀,
        ‖hess f x - hess f xstar‖ ≤ κ * ‖x - xstar‖)
    (χα : ℝ) (hχ : 0 ≤ χα) :
    ∃ r : ℝ, 0 < r ∧ ∃ C : ℝ,
      ∀ (x : ℕ → ReflNewton.FirstOrder.E n) (α : ℕ → ℝ),
        IsLocalNewtonRun l u f χα x α →
        x 0 ∈ Metric.ball xstar r →
        (∀ k, x k ∈ ReflNewton.FirstOrder.intBox l u) ∧
        (∀ k, ‖x (k + 1) - xstar‖ ≤ C * ‖x k - xstar‖ ^ 2) ∧
        Filter.Tendsto x Filter.atTop (nhds xstar) := by sorry

end ReflNewton.LocalQuad
