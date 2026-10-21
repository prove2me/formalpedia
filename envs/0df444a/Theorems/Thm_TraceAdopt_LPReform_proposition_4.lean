-- Prove2me | Theorems.Thm_TraceAdopt_LPReform_proposition_4
-- name    : TraceAdopt.LPReform.proposition_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:36:39.051333+00:00
-- url     : https://prove2.me/theorems/c5684afe-7ed6-4383-bb4e-a84577ea04b0
-- title:
--   Proposition 4, p. 15 — bounded-treewidth binary programs have small LP formulations
-- statement:
--   Consider a binary linear program $\min\{c^Tx:Ax\ge b,\ x\in\{0,1\}^n\}$. If its intersection graph has treewidth at most $\omega$, then one absolute constant $C>0$ bounds the size of an equivalent linear-programming extended formulation by $C2^\omega(n+1)$, counting both variables and constraints. Its projection onto the original $x$ coordinates is the convex hull of the binary feasible vectors:
--
--   $$\operatorname{proj}_x(P)=\operatorname{conv}\{x\in\{0,1\}^n:Ax\ge b\}.$$
--
--   The same feasible region works for every objective $c$. This is the general result cited from Laurent and from Bienstock–Muñoz, used to convert a bounded-treewidth BiLP into an LP.
--
--   **Formalization Note** The absolute constant precedes all instance parameters. The replacement of $n$ by $n+1$ includes the empty-variable case without changing the stated asymptotic size class.
-- source:
--   Blaettchen, Calmon & Hall, Traceability Technology Adoption in Supply Chain Networks, arXiv:2104.14818v4, p. 15, Proposition 4, equation (3), Definition 4; Laurent 2009; Bienstock & Muñoz 2018

import Definitions.Def_TraceAdopt_LPReform_LinearSystem
import Definitions.Def_RobertsonSeymour1986_GM5_TreewidthLE

namespace TraceAdopt.LPReform

/-- Proposition 4, p. 15: a binary linear system whose intersection graph
has treewidth at most `ω` admits a size-`O(2^ω n)` LP extended formulation. -/
theorem proposition_4 :
    ∃ C : ℕ, 0 < C ∧
      ∀ (n m : ℕ) (A : Matrix (Fin m) (Fin n) ℝ)
        (b : Fin m → ℝ) (ω : ℕ),
        RobertsonSeymour1986.GM5.TreewidthLE
          (intersectionGraph
            (fun k : Fin m => Finset.univ.filter (fun i : Fin n => A k i ≠ 0))) ω →
        ∃ (N K : ℕ) (A' : Matrix (Fin K) (Fin n ⊕ Fin N) ℝ)
          (b' : Fin K → ℝ),
          n + N + K ≤ C * 2 ^ ω * (n + 1) ∧
          {x : Fin n → ℝ | ∃ y : Fin N → ℝ, LinFeasible A' b' x y} =
            convexHull ℝ {x : Fin n → ℝ |
              (∀ i, x i = 0 ∨ x i = 1) ∧
              ∀ k, b k ≤ A.mulVec x k} := by sorry

end TraceAdopt.LPReform
