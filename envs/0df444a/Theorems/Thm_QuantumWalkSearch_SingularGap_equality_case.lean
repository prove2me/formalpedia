-- Prove2me | Theorems.Thm_QuantumWalkSearch_SingularGap_equality_case
-- name    : QuantumWalkSearch.SingularGap.equality_case
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T08:41:54.225882+00:00
-- url     : https://prove2.me/theorems/e8eff3ef-05d4-45ea-8260-381344440770
-- title:
--   Proof of Proposition 3, p. 20 — u†D(P)w = 1 forces u_x = w_y √(π_x/π_y) whenever p_{xy} > 0
-- statement:
--   Let $P=(p_{xy})_{x,y\in X}$ be an irreducible Markov chain on a finite state space $X$ with stationary distribution $\pi$, and $D(P)=\operatorname{diag}(\pi)^{1/2}P\operatorname{diag}(\pi)^{-1/2}$. Let $u,w\in\mathbb C^X$ be unit vectors with
--   $$u^\dagger D(P)\,w=1 .$$
--   Then for every pair $x,y\in X$ with $p_{xy}>0$,
--   $$u_x=w_y\sqrt{\frac{\pi_x}{\pi_y}} .$$
--
--   This is the equality case of the Cauchy–Schwarz inequality (9): equality forces the vectors $u'=(u_x\sqrt{p_{xy}})_{x,y}$ and $w'=(w_y\sqrt{\pi_xp_{xy}/\pi_y})_{x,y}$ in $\mathbb C^{X\times X}$ to coincide. It is the first step in showing that the singular value $1$ of $D(P)$ is simple.
--
--   **Formalization Note** $u^\dagger D(P)w$ is Mathlib's inner product `inner ℂ u (D(P) w)`, conjugate-linear in $u$. Because the hypothesis is that this inner product equals the real number $1$ exactly (not merely in absolute value), the paper's "ignoring an overall phase" is not needed: the conclusion holds with no phase factor.
-- source:
--   Magniez, Nayak, Roland, Santha, Search via Quantum Walk, arXiv:quant-ph/0608026v4, p. 20, proof of Proposition 3 (equality case of Equation (9))

import Mathlib
import Definitions.Def_QuantumWalkSearch_SingularGap_Discriminant

open Matrix

namespace QuantumWalkSearch.SingularGap

theorem equality_case {X : Type*} [Fintype X] [DecidableEq X]
    (P : Matrix X X ℝ) (π : X → ℝ)
    (hP : P ∈ Matrix.rowStochastic ℝ X) (hirr : P.IsIrreducible)
    (hπ : IsStationaryDistribution P π)
    (u w : EuclideanSpace ℂ X) (hu : ‖u‖ = 1) (hw : ‖w‖ = 1)
    (h1 : inner ℂ u (discriminantOp P π w) = 1) :
    ∀ x y : X, 0 < P x y → u x = w y * ((Real.sqrt (π x / π y) : ℝ) : ℂ) := by sorry

end QuantumWalkSearch.SingularGap
