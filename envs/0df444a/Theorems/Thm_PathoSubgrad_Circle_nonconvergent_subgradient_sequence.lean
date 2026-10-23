-- Prove2me | Theorems.Thm_PathoSubgrad_Circle_nonconvergent_subgradient_sequence
-- name    : PathoSubgrad.Circle.nonconvergent_subgradient_sequence
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T07:22:50.320832+00:00
-- url     : https://prove2.me/theorems/ce1d3b3b-08e3-4914-b448-f8f6cf34e1db
-- title:
--   Q9, p. 4 (with Q1, p. 3; §2, p. 5) — a Whitney C^∞-stratifiable, path-differentiable Kurdyka–Łojasiewicz function on R² with a bounded subgradient sequence that does not converge
-- statement:
--   There exist a function $f:\mathbb R^2\to\mathbb R$, positive step sizes $(\varepsilon_i)_{i\ge0}$ and a sequence $(x_i)_{i\ge0}$ in $\mathbb R^2$ such that:
--
--   1. $(x_i)$ is a subgradient sequence of $f$ with step sizes $(\varepsilon_i)$ (Definition 1: $f$ locally Lipschitz, $\varepsilon_i\to0$, $\sum_i\varepsilon_i=+\infty$, $x_{i+1}=x_i-\varepsilon_i v_i$ with $v_i\in\partial^c f(x_i)$);
--   2. $(x_i)$ is bounded and does **not** converge;
--   3. $f$ is Lipschitz and path-differentiable (Definition 2);
--   4. $f$ satisfies the weak Sard condition (Definition 3);
--   5. $f$ is Whitney $C^\infty$-stratifiable (Definition 5);
--   6. $f$ satisfies the Kurdyka–Łojasiewicz inequality
--   $$\|\nabla f(x)\|\ge\frac12\qquad\text{for all } x\notin\operatorname{crit}f;$$
--   7. each point $x_i$ has a ball around it on which $f$ is $C^\infty$.
--
--   This answers Q9 of the paper negatively: Whitney stratifiability together with a Kurdyka–Łojasiewicz inequality does not imply convergence of bounded small-step subgradient sequences, even under the weak Sard condition (Q1), and even when every iterate lies in a region where $f$ is smooth (Q12). It contrasts with the continuous-time subgradient flow, which converges under the weak Sard condition and the Kurdyka–Łojasiewicz inequality.
--
--   **Formalization Note.** The witness is existentially quantified; the paper's witness is the function (4) with $i_0$ large and $x_k=x_{i_0+k}$, the subject of the milestones. Because Lean's `gradient` is $0$ where $f$ is not differentiable, item 6 also asserts that $f$ is differentiable at every non-critical point. The Clarke subdifferential and the other notions are those of `PathoSubgrad.Circle.Setting`.
-- source:
--   Ríos-Zertuche, Examples of pathological dynamics of the subgradient method for Lipschitz path-differentiable functions, arXiv:2007.11699v1, p. 4, Q9 (with p. 3, Q1; p. 5, §2 and Q12)

import Mathlib
import Definitions.Def_PathoSubgrad_Circle_Setting
import Definitions.Def_PathoSubgrad_Circle_Construction

open Filter Topology
open scoped InnerProductSpace ContDiff

namespace PathoSubgrad.Circle

theorem nonconvergent_subgradient_sequence :
    ∃ (f : EuclideanSpace ℝ (Fin 2) → ℝ) (ε : ℕ → ℝ) (x : ℕ → EuclideanSpace ℝ (Fin 2)),
      IsSubgradientSeq f ε x ∧ Bornology.IsBounded (Set.range x) ∧
      (¬ ∃ p, Tendsto x atTop (𝓝 p)) ∧
      (∃ K, LipschitzWith K f) ∧ IsPathDifferentiable f ∧ WeakSard f ∧
      IsWhitneyCInfStratifiable f ∧
      (∀ y ∉ critSet f, DifferentiableAt ℝ f y ∧ 1 / 2 ≤ ‖gradient f y‖) ∧
      (∀ i, ∃ r > 0, ContDiffOn ℝ ∞ f (Metric.ball (x i) r)) := by sorry

end PathoSubgrad.Circle
