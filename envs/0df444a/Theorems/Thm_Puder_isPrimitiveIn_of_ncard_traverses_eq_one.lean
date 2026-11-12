-- Prove2me | Theorems.Thm_Puder_isPrimitiveIn_of_ncard_traverses_eq_one
-- name    : Puder.isPrimitiveIn_of_ncard_traverses_eq_one
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T19:05:07.51903+00:00
-- url     : https://prove2.me/theorems/2760c631-bc31-4366-8497-7183f287afd5
-- title:
--   Puder, proof of Lemma 4.1 — if the walk of w ∈ N crosses some edge exactly once, then w is primitive in N
-- statement:
--   Let $N \le \mathbf F_d$ be finitely generated (`Subgroup.FG`) and $w \in N$. Suppose that the reduced walk of $w$ from the basepoint of the Schreier coset graph of $N$ crosses the $x$-labelled edge leaving the coset $Ng$ at exactly one position (`Puder.Traverses N w i g x` for exactly one $i$). Then $w$ is primitive in $N$ (`Puder.IsPrimitiveIn N w`): $w$ belongs to some basis of $N$.
--
--   Puder, pp. 14–15, proof of Lemma 4.1: “Next, we distinguish between *separating* edges and *non-separating* edges in $\Gamma = \Gamma_X(N)$. If $e$ is a separating edge, namely if removing $e$ separates $\Gamma$ into two connected components, then it is obvious that the walk of $w$ in $\Gamma$ must traverse $e$ an even number of times, and since this number is $\ge 1$, it is in fact $\ge 2$.
--   Finally, assume that $e$ is not separating, and $w$ traverses it exactly once, so that the walk corresponding to $w$ in $\Gamma_X(N)$ is $w_1 e w_2$ (with $w_1, w_2$ avoiding $e$; we think of $e$ as oriented according to the direction of $w$). Choose a spanning tree $T$ of $\Gamma_X(N)$ which avoids $e$ to obtain a basis for $N$ as follows. […] We claim that so is $\{w, u_2, \ldots, u_r\}$, so that $w$ is primitive in $N$ and therefore $\langle w \rangle \le_{ff} N$, a contradiction.”
--
--   *Formalization note.* The two cases of the source (a separating edge is crossed an even number of times; a non-separating edge crossed once makes $w$ primitive) are stated together as their joint consequence: an edge crossed exactly once makes $w$ primitive in $N$. The source's $w$ is a proper algebraic extension's generator; the statement needs only $w \in N$.
--
--   Source: D. Puder, *Expansion of random graphs: new proofs, new results*, Invent. Math. 201 (2015) 845–908, https://doi.org/10.1007/s00222-014-0560-x (arXiv:1212.5216, pp. 14–15), proof of Lemma 4.1.
-- source:
--   Puder, D., Expansion of random graphs: new proofs, new results, Invent. Math. 201 (2015) 845–908, https://doi.org/10.1007/s00222-014-0560-x (arXiv:1212.5216), pp. 14–15, proof of Lemma 4.1 (an edge traversed exactly once makes w primitive in N)

import Mathlib
import Definitions.Def_StrongConvPuder
import Definitions.Def_StrongConvPuderCore

namespace Puder

theorem isPrimitiveIn_of_ncard_traverses_eq_one {d : ℕ} (N : Subgroup (FreeGroup (Fin d))) (hN : N.FG)
    (w : FreeGroup (Fin d)) (hw : w ∈ N) (g : FreeGroup (Fin d)) (x : Fin d)
    (h1 : {i : ℕ | Traverses N w i g x}.ncard = 1) : IsPrimitiveIn N w := by
  sorry

end Puder
