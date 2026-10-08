-- Prove2me | Theorems.Thm_QuantumWalkSearch_SingularGap_eq_9
-- name    : QuantumWalkSearch.SingularGap.eq_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T08:41:23.34503+00:00
-- url     : https://prove2.me/theorems/b21ac3c8-ff18-4627-9af1-68e1a6409898
-- title:
--   Eq. (9) — Cauchy–Schwarz bound |u†D(P)v| ≤ 1 for unit vectors u, v
-- statement:
--   Let $P=(p_{xy})_{x,y\in X}$ be an irreducible Markov chain on a finite state space $X$ with stationary distribution $\pi$, and let $D(P)=\operatorname{diag}(\pi)^{1/2}P\operatorname{diag}(\pi)^{-1/2}$ be its discriminant. For all unit vectors $u,v\in\mathbb C^X$,
--   $$\bigl|u^\dagger D(P)v\bigr|=\Bigl|\sum_{x,y}\overline{u_x}\,v_y\sqrt{\tfrac{\pi_x}{\pi_y}}\,p_{xy}\Bigr|\le\Bigl(\sum_{x,y}|u_x|^2p_{xy}\Bigr)^{1/2}\Bigl(\sum_{x,y}|v_y|^2\tfrac{\pi_x}{\pi_y}\,p_{xy}\Bigr)^{1/2}\le1 .$$
--
--   The statement consists of three parts: the expansion of $u^\dagger D(P)v$ as a double sum, the Cauchy–Schwarz bound by the product of the two square roots, and the bound of that product by $1$ (the first factor equals $\|u\|=1$ because rows of $P$ sum to one, the second equals $\|v\|=1$ because $\sum_x\pi_xp_{xy}=\pi_y$).
--
--   This inequality shows that the operator norm of $D(P)$ is at most $1$ (Lemma 3), and its equality case is the heart of the proof of Proposition 3.
--
--   **Formalization Note** $u^\dagger D(P)v$ is Mathlib's inner product `inner ℂ u (D(P) v)`, conjugate-linear in $u$. The middle expression is stated with real square roots of the two real double sums.
-- source:
--   Magniez, Nayak, Roland, Santha, Search via Quantum Walk, arXiv:quant-ph/0608026v4, p. 20, Equation (9) (proof of Lemma 3)

import Mathlib
import Definitions.Def_QuantumWalkSearch_SingularGap_Discriminant

open Matrix

namespace QuantumWalkSearch.SingularGap

theorem eq_9 {X : Type*} [Fintype X] [DecidableEq X]
    (P : Matrix X X ℝ) (π : X → ℝ)
    (hP : P ∈ Matrix.rowStochastic ℝ X) (hirr : P.IsIrreducible)
    (hπ : IsStationaryDistribution P π)
    (u v : EuclideanSpace ℂ X) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) :
    inner ℂ u (discriminantOp P π v) =
        ∑ x, ∑ y, star (u x) * v y * ((Real.sqrt (π x / π y) * P x y : ℝ) : ℂ) ∧
      ‖inner ℂ u (discriminantOp P π v)‖ ≤
        Real.sqrt (∑ x, ∑ y, ‖u x‖ ^ 2 * P x y) *
          Real.sqrt (∑ x, ∑ y, ‖v y‖ ^ 2 * (π x / π y) * P x y) ∧
      Real.sqrt (∑ x, ∑ y, ‖u x‖ ^ 2 * P x y) *
          Real.sqrt (∑ x, ∑ y, ‖v y‖ ^ 2 * (π x / π y) * P x y) ≤ 1 := by sorry

end QuantumWalkSearch.SingularGap
