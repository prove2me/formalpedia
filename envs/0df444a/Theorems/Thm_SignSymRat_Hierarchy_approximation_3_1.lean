-- Prove2me | Theorems.Thm_SignSymRat_Hierarchy_approximation_3_1
-- name    : SignSymRat.Hierarchy.approximation_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:06:51.537996+00:00
-- url     : https://prove2.me/theorems/caf97031-7b80-46bf-a4c8-e465b52712f8
-- title:
--   Proof of Theorem 3.1 — two-sided polynomial approximation
-- statement:
--   Under Assumption 1.1, let $N\ge2$, choose any $\varepsilon>0$, and choose a ratio other than the distinguished first ratio. There is a polynomial $h_i$ satisfying, at every $x\in K$,
--
--   $$\frac{p_i(x)}{q_i(x)}-\frac{\varepsilon}{N-1}\le h_i(x)\le\frac{p_i(x)}{q_i(x)}.$$
--
--   The claim is the paper's uniform polynomial approximation from below, used to compare the dual with the original infimum.
--
--   **Formalization Note** The paper's $i=1$ is Lean's index `0`, so the selected ratio satisfies `i ≠ 0`. The explicit $N\ge2$ makes the denominator $N-1$ positive.
-- source:
--   Guo, Wang & Zheng, Exploiting Sign Symmetries in Minimizing Sums of Rational Functions, arXiv:2405.09419v1, p. 6, proof of Theorem 3.1, Stone–Weierstrass approximation display

import Mathlib
import Definitions.Def_SignSymRat_Hierarchy_Setting

open MvPolynomial

namespace SignSymRat.Hierarchy

/-- The two-sided polynomial approximation in the proof of Theorem 3.1, p. 6. -/
theorem approximation_3_1 {n m N : ℕ} (P : SRFO n m N)
    [NeZero N] (hN : 2 ≤ N) (hA : P.Assumption11) :
    ∀ ε : ℝ, 0 < ε → ∀ i : Fin N, i ≠ 0 →
      ∃ h : MvPolynomial (Fin n) ℝ, ∀ x ∈ P.K,
        eval x (P.p i) / eval x (P.q i) - ε / ((N - 1 : ℕ) : ℝ) ≤ eval x h ∧
        eval x h ≤ eval x (P.p i) / eval x (P.q i) := by sorry

end SignSymRat.Hierarchy
