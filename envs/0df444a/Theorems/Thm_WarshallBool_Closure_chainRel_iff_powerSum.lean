-- Prove2me | Theorems.Thm_WarshallBool_Closure_chainRel_iff_powerSum
-- name    : WarshallBool.Closure.chainRel_iff_powerSum
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T15:54:11.630162+00:00
-- url     : https://prove2.me/theorems/3fe630f1-db4b-4b21-aa00-eafba32e2e7e
-- title:
--   Footnote 2, p. 11 — the chain definition of $M'$ agrees with $\bigvee_{i=1}^d M^i$
-- statement:
--   Let $M = (m_{ij})$ be a $d \times d$ matrix with entries in $\{0,1\}$, and let $i, j$ be indices. Write $M^p$ for the boolean powers of $M$ ($M^1 = M$, $M^{p+1} = M^p \wedge M$, with $(A \wedge B)_{ij} = \bigvee_k (a_{ik} \wedge b_{kj})$).
--
--   Then either $m_{ij} = 1$ or there are indices $k_1, \dots, k_n$ with $m_{ik_1} = m_{k_1k_2} = \cdots = m_{k_nj} = 1$, if and only if
--   $$
--   \Bigl(\bigvee_{p=1}^{d} M^p\Bigr)_{ij} = 1 .
--   $$
--
--   This is footnote 2 of Warshall's note: the THEOREM's chain definition of $M'$ "is trivially equivalent to" the introduction's $M' = \bigvee_{i=1}^d M^i$. The content beyond unfolding definitions is that chains may be taken of length at most $d$, so that the powers up to $M^d$ suffice.
--
--   **Formalization Note** Indices run over $\{0, \dots, d-1\}$ instead of $\{1, \dots, d\}$, and $1$ is `true`. The chain side is the proposition that some (possibly empty) list $k_1, \dots, k_n$ of indices makes $i, k_1, \dots, k_n, j$ a chain of entries equal to $1$; the empty list is the case $m_{ij} = 1$. There is no reflexive closure on either side.
-- source:
--   Warshall, A theorem on Boolean matrices, J. ACM 9 (1962), p. 11, THEOREM (definition of M′) and footnote 2 ('This definition of M′ is trivially equivalent to the previous one'), with the introduction's display M′ = ∨_{i=1}^d M^i

import Mathlib
import Definitions.Def_WarshallBool_Closure_Setting

namespace WarshallBool.Closure

/-- Warshall (1962), p. 11, footnote 2: the chain definition of `M′` in the THEOREM agrees
with the introduction's `M′ = ∨_{p=1}^{d} M^p`. -/
theorem chainRel_iff_powerSum {d : ℕ} (M : Fin d → Fin d → Bool) (i j : Fin d) :
    ChainRel M i j ↔ powerSum M i j = true := by sorry

end WarshallBool.Closure
