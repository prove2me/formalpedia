-- Prove2me | Theorems.Thm_RobustSDP_FullPert_Supplement_theorem_4_3
-- name    : RobustSDP.FullPert.Supplement.theorem_4_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T00:46:47.420527+00:00
-- url     : https://prove2.me/theorems/e53939b1-e501-4173-a1fa-ff70d9b1589e
-- title:
--   Theorem 4.3 — Hölder stability of all O(‖u‖)-suboptimal solutions
-- statement:
--   Let $P(u)$ be the SDP (15) with coefficientwise $C^1$ data $F_i(u),R_i(u),L(u)$ near $u=0$, with symmetric $F_i(u)$ and fixed $c\ne0$. Suppose H1 (strict feasibility), H2 (bounded feasible objective sublevels), and both clauses of H3 hold at zero. There exists an optimal decision $x_0$ of $P(0)$ such that for every nonnegative accuracy function $\varepsilon=O(\|u\|)$ there are $\gamma,\delta>0$ with
--   $$\|x-x_0\|_2\le\gamma\|u\|_2^{1/2}$$
--   for all $\|u\|_2<\delta$ and all $\varepsilon(u)$-suboptimal decisions of $P(u)$. Feasibility of a decision means existence of an auxiliary $\tau$. This includes exact solutions by taking zero accuracy. **Formalization Note.** Big-O has its standard existential local bound; the constants may depend on the accuracy function and data family. No numerical value for them is required or asserted.
--
--   Differences from the source:
--   - encoding: ϵ = O(u) and a neighborhood V of zero → a nonnegative function with an existential eventual O(‖u‖) bound and an open Euclidean ball; reason: this is the standard meaning of the printed qualitative asymptotic estimate; it retains arbitrary accuracy budgets and finite-dimensional C1 data families.
-- source:
--   El Ghaoui, Oustry and Lebret, Robust Solutions to Uncertain Semidefinite Programs, SIAM J. Optim. 9(1) (1998), p. 40, Theorem 4.3

import Mathlib
import Definitions.Def_RobustSDP_FullPert_Supplement_Regularity

open Matrix

namespace RobustSDP.FullPert.Supplement

/-- Theorem 4.3, p. 40: all O(norm u)-suboptimal projected solutions of the C1 data
family satisfy (18). The big-O constant and the neighborhood are existential.
No prescribed numerical tolerance constant is an assumption of the source. -/
theorem theorem_4_3 {k m n p q : ℕ}
    (A : Param k → RobustSDP.Uniqueness.SDPData m n p q) (c : Fin m → ℝ)
    (hc : c ≠ 0) (hC1 : SmoothSDPFamily A)
    (h1 : (A 0).Slater) (h2 : (A 0).InfCompact c)
    (h3a : (A 0).H3a) (h3b : (A 0).H3b) :
    ∃ x0 : Fin m → ℝ, LinearOptimal (projected15 (A 0)) c x0 ∧
      HolderRegular (fun u => projected15 (A u)) c x0 := by sorry

end RobustSDP.FullPert.Supplement
