-- Prove2me | Theorems.Thm_SaturatedNet_Uniqueness_proposition_3
-- name    : SaturatedNet.Uniqueness.proposition_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T12:37:29.989516+00:00
-- url     : https://prove2.me/theorems/e112020d-30f8-4b21-8804-07d491f6c5b0
-- title:
--   Proposition 3, p. 10 — a positive v with Pv ≤ v exists iff ρ(P) < 1, or ρ(P) = 1 and every basic class is final
-- statement:
--   Let $P \in \mathbb R_+^{n \times n}$ be a nonnegative square matrix. Then there is a positive vector
--   $v$ (all entries $v_i > 0$) with
--
--   $$Pv \le v$$
--
--   if and only if either $\rho(P) < 1$, or $\rho(P) = 1$ and every basic class of $P$ is final. Here a
--   class is a strongly connected component $V$ of the digraph $\mathcal G_P$; it is basic when the
--   principal block $P^{(VV)}$ has $\rho(P^{(VV)}) = \rho(P)$ and final when no link of
--   $\mathcal G_P$ leaves $V$.
--
--   The right-hand side is the definition of a non-expansive network (Definition 1). A positive $v$ with
--   $Pv \le v$ yields the weighted $\ell_1$-norm $\|x\| = \sum_i v_i |x_i|$ in which $x \mapsto
--   S_0^w(P^\top x + c)$ is non-expansive; this is the engine of Theorem 1.
-- source:
--   Massai, Como & Fagnani, Equilibria and Systemic Risk in Saturated Networks, arXiv:1912.04815v2, p. 10, Proposition 3 (proof pp. 25–26)

import Mathlib
import Definitions.Def_SaturatedNet_Uniqueness_Model
open Matrix

namespace SaturatedNet.Uniqueness

theorem proposition_3 {n : Type*} [Fintype n] [DecidableEq n]
    (P : Matrix n n ℝ) (hP : ∀ i j, 0 ≤ P i j) :
    (∃ v : n → ℝ, (∀ i, 0 < v i) ∧ P *ᵥ v ≤ v) ↔
      (specRad P < 1 ∨
        (specRad P = 1 ∧ ∀ V : Finset n, IsClass P V → IsBasic P V → IsFinal P V)) := by sorry

end SaturatedNet.Uniqueness
