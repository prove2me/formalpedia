-- Prove2me | Theorems.Thm_WarshallBool_Closure_warshall_eq_powerSum
-- name    : WarshallBool.Closure.warshall_eq_powerSum
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T15:54:25.486082+00:00
-- url     : https://prove2.me/theorems/ecaa27e9-4d5c-4b12-8e32-2086fd47835e
-- title:
--   Introduction and THEOREM, p. 11 — Warshall's construction $M^*$ equals $M \vee M^2 \vee \cdots \vee M^d$
-- statement:
--   Let $M = (m_{ij})$ be a $d \times d$ matrix each of whose entries is $0$ or $1$. Warshall's construction produces a matrix $M^*$ as follows: set $M^* = M$; then for $i = 1, 2, \dots, d$ in turn, for every row $j$ with $m^*_{ji} = 1$ and every column $k$, set $m^*_{jk} = m^*_{jk} \vee m^*_{ik}$.
--
--   Let $M^1 = M$ and $M^{p+1} = M^p \wedge M$ be the boolean powers of $M$, where the boolean product is $(A \wedge B)_{ij} = \bigvee_k (a_{ik} \wedge b_{kj})$. Then
--   $$
--   M^* \;=\; \bigvee_{p=1}^{d} M^p \;=\; M \vee M^2 \vee \cdots \vee M^d ,
--   $$
--   the boolean sum being taken entrywise.
--
--   This is the claim Warshall's note sets out to establish: the introduction poses the problem of transforming $M$ into $M' = \bigvee_{i=1}^d M^i$, the THEOREM asserts $M^* = M'$ for the chain definition of $M'$, and footnote 2 identifies the two definitions. It shows that the $d$-pass construction, with on the order of $d^2$ row operations, computes the transitive closure that the power sum computes with $d$ boolean matrix products.
--
--   **Formalization Note** Matrices are functions $\mathrm{Fin}\,d \to \mathrm{Fin}\,d \to \mathrm{Bool}$ with $1$ as `true`, indexed $0, \dots, d-1$. $M^*$ is the published definition `FloydAlgorithms.ShortestPath.algorithm96` (Floyd's Algorithm 96 is Warshall's construction, with the inner loops over $j$ and $k$ in ascending order, which does not change the result). The power sum runs over $p \in \{1, \dots, d\}$ with the page's exponents; no identity matrix (reflexive closure) is included. The boolean product is defined by "there exists $k$", not by Mathlib's matrix product over `Bool`, whose addition is exclusive or. The case $d = 0$ is allowed and is trivial.
-- source:
--   Warshall, A theorem on Boolean matrices, J. ACM 9 (1962), p. 11, introduction (display M′ = ∨_{i=1}^d M^i), THEOREM ('We assert M* = M′') and footnote 2

import Mathlib
import Definitions.Def_FloydAlgorithms_ShortestPath_Algorithm96
import Definitions.Def_WarshallBool_Closure_Setting

namespace WarshallBool.Closure

/-- Warshall (1962), p. 11, introduction display with the THEOREM ("We assert M* = M′") and
footnote 2: Warshall's construction `M*` (steps 0–4) equals `M ∨ M^2 ∨ ⋯ ∨ M^d`. -/
theorem warshall_eq_powerSum {d : ℕ} (M : Fin d → Fin d → Bool) :
    FloydAlgorithms.ShortestPath.algorithm96 M = powerSum M := by sorry

end WarshallBool.Closure
