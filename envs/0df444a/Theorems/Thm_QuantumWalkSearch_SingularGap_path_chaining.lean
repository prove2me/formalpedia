-- Prove2me | Theorems.Thm_QuantumWalkSearch_SingularGap_path_chaining
-- name    : QuantumWalkSearch.SingularGap.path_chaining
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T08:42:09.839995+00:00
-- url     : https://prove2.me/theorems/e819aad3-7cf2-41c7-a2e8-787d9487a334
-- title:
--   Proof of Proposition 3, pp. 20–21 — chaining u_{x_{i+1}} = u_{x_i}√(π_{x_{i+1}}/π_{x_i}) along paths gives u_y = u_{x_1}√(π_y/π_{x_1})
-- statement:
--   Let $P=(p_{xy})_{x,y\in X}$ be an irreducible Markov chain on a finite state space $X$ with stationary distribution $\pi$, and let $u\in\mathbb C^X$ satisfy
--   $$u_y=u_x\sqrt{\frac{\pi_y}{\pi_x}}\qquad\text{for every pair }x,y\in X\text{ with }p_{xy}>0,$$
--   that is, along every edge $x\to y$ of the graph underlying the chain. Then for all $x_1,y\in X$,
--   $$u_y=u_{x_1}\sqrt{\frac{\pi_y}{\pi_{x_1}}} .$$
--
--   Chaining the edge relation along a path $x_1,x_2,\dots,x_k$ gives $u_{x_i}=u_{x_1}\sqrt{\pi_{x_i}/\pi_{x_1}}$, and irreducibility (strong connectivity of the graph) supplies a path from $x_1$ to every $y$. In particular $u$ is a scalar multiple of $v=(\sqrt{\pi_x})_x$, which is how the proof of Proposition 3 concludes.
--
--   **Formalization Note** The graph underlying the chain has an edge $x\to y$ exactly when $p_{xy}>0$ (Mathlib's `Matrix.toQuiver`), and irreducibility is Mathlib's `Matrix.IsIrreducible`.
-- source:
--   Magniez, Nayak, Roland, Santha, Search via Quantum Walk, arXiv:quant-ph/0608026v4, pp. 20-21, proof of Proposition 3 (path chaining)

import Mathlib
import Definitions.Def_QuantumWalkSearch_SingularGap_Discriminant

open Matrix

namespace QuantumWalkSearch.SingularGap

theorem path_chaining {X : Type*} [Fintype X] [DecidableEq X]
    (P : Matrix X X ℝ) (π : X → ℝ)
    (hP : P ∈ Matrix.rowStochastic ℝ X) (hirr : P.IsIrreducible)
    (hπ : IsStationaryDistribution P π)
    (u : X → ℂ)
    (hu : ∀ x y : X, 0 < P x y → u y = u x * ((Real.sqrt (π y / π x) : ℝ) : ℂ)) :
    ∀ x₁ y : X, u y = u x₁ * ((Real.sqrt (π y / π x₁) : ℝ) : ℂ) := by sorry

end QuantumWalkSearch.SingularGap
