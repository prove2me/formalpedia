-- Prove2me | Theorems.Thm_SelfDualLP_Complexity_termination_claim
-- name    : SelfDualLP.Complexity.termination_claim
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T18:00:42.87217+00:00
-- url     : https://prove2.me/theorems/49e49f4f-ae37-4283-9fbd-ffc0baaeafd0
-- title:
--   Proof of Theorem 6, termination — once $x^Ts+\tau\kappa\le2^{-O(L)}$ in $\mathcal N(1/2)$, the projection is exactly strictly self-complementary
-- statement:
--   There is an absolute constant $C'>0$ with the following property. Let $A\in\mathbb Z^{m\times n}$, $b\in\mathbb Z^m$, $c\in\mathbb Z^n$ be integer data with $n\ge1$ and bit length $L$, and let $z=(y,x,\tau,\theta,s,\kappa)$ be a point of $\mathcal N(1/2)$ for (HLP) under the choice (7) with
--   $$
--   x^Ts+\tau\kappa\le 2^{-C'L}.
--   $$
--   Then the least-squares termination projection at $z$ has an output, and every output $u$, rescaled to the normalization (9), is a strictly self-complementary solution of (HLP).
--
--   This is the step that turns an approximate iterate into an exact solution after finitely many iterations.
--
--   **Formalization Note** The paper's threshold $2^{-O(L)}$ is pinned as $2^{-C'L}$ with $C'$ absolute (independent of $m,n,A,b,c$ and $z$); the paper states it for iterates, and the claim is formalized for every point of $\mathcal N(2\beta)=\mathcal N(1/2)$, which is how the cited results of Mehrotra–Ye (1991) and Ye (1993) apply. The projection output is rescaled by $(n+1)/(e^Tx^*+e^Ts^*+\tau^*+\kappa^*)$ because the projection imposes only the homogeneous rows; without the rescaling the claim is false.
-- source:
--   Ye, Todd, Mizuno, An O(√nL)-Iteration Homogeneous and Self-Dual Linear Programming Algorithm, Math. Oper. Res. 19(1) (1994), p. 62, proof of Theorem 6 (termination claim); termination technique on p. 61

import Mathlib
import Definitions.Def_SelfDualLP_Complexity_HLP
import Definitions.Def_SelfDualLP_Complexity_Neighborhood
import Definitions.Def_SelfDualLP_Complexity_Termination
import Definitions.Def_SelfDualLP_Complexity_BitLength

open Matrix

namespace SelfDualLP.Complexity

/-- Proof of Theorem 6, termination claim (p. 62), with `2^{−O(L)}` pinned as `2^{−C'L}` for an
absolute constant `C' > 0`. For integer data `(A, b, c)` with `n ≥ 1` and bit length `L`, and
every point `z ∈ 𝒩(1/2)` of (HLP) under (7) with `xᵀs + τκ ≤ 2^{−C'L}`, the least-squares
termination projection at `z` has an output, and every output `u`, rescaled to the
normalization (9), is a strictly self-complementary solution of (HLP). -/
theorem termination_claim :
    ∃ C' : ℝ, 0 < C' ∧ ∀ (m n : ℕ), 1 ≤ n →
      ∀ (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ) (c : Fin n → ℤ) (z : HLPPoint m n),
        Nbhd (castMat A) (castVec b) (castVec c) (1 / 2) z →
        gap z ≤ (2 : ℝ) ^ (-(C' * (bitLength A b c : ℝ))) →
        (∃ u, IsTerminationOutput (castMat A) (castVec b) (castVec c) z u) ∧
        ∀ u, IsTerminationOutput (castMat A) (castVec b) (castVec c) z u →
          StrictlySelfComplementary7 (castMat A) (castVec b) (castVec c) (rescaleOutput u) := by sorry

end SelfDualLP.Complexity
