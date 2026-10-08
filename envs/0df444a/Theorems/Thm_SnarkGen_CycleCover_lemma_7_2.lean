-- Prove2me | Theorems.Thm_SnarkGen_CycleCover_lemma_7_2
-- name    : SnarkGen.CycleCover.lemma_7_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T18:06:23.902014+00:00
-- url     : https://prove2.me/theorems/cbb2c701-9a96-4a84-994f-4385d175658c
-- title:
--   Lemma 7.2 — a 2-regular subgraph C in a CDC gives a cycle cover of length at most 2m − |C|
-- statement:
--   Let $G$ be a finite simple cubic graph with $m$ edges. Suppose $C$ is a $2$-regular subgraph of $G$ and $\mathcal D = (D_0,\dots,D_{k-1})$ is a CDC of $G$ in which $C$ occurs: each $D_j$ is an even subgraph of $G$, every edge of $G$ lies in exactly two members of $\mathcal D$ (counted with multiplicity), and $D_i = C$ for some index $i$. Then $G$ has a cycle cover $\mathcal F$ with
--
--   $$\ell(\mathcal F) \le 2m - |C| .$$
--
--   In particular the shortest cycle cover of $G$ has length at most $2m - |C|$. The paper applies the lemma with $C$ a $2$-factor and $\mathcal D$ the $4$-CDC of Proposition 5.3.
--
--   **Formalization Note** The CDC is taken as a family of even subgraphs, the form the paper calls "often convenient" and the form in which it applies the lemma; a CDC of cycles containing $C$ (so $C$ a single cycle) is the special case where each cycle is its own member, so this statement contains the literal one. Since $|C| \le m$, the bound is written $\ell(\mathcal F) + |C| \le 2m$ to avoid truncated subtraction in $\mathbb N$. A shortest cycle cover exists because $G$ has finitely many cycle covers, so bounding it is equivalent to exhibiting one cover that meets the bound. The cubic hypothesis is kept as printed.
-- source:
--   G. Brinkmann, J. Goedgebeur, J. Hägglund, K. Markström, Generation and properties of snarks, arXiv:1206.6690v3, p. 24, Lemma 7.2

import Mathlib
import Definitions.Def_SnarkGen_CycleCover_IsTwoRegularEdgeSet
import Definitions.Def_SnarkGen_CycleCover_IsKCDCEven
import Definitions.Def_SnarkGen_CycleCover_IsCycleCover

namespace SnarkGen.CycleCover

/-- arXiv:1206.6690v3, Lemma 7.2 (p. 24): if a cubic graph `G` has a 2-regular subgraph `C`
and a CDC `𝒟` (as a family of even subgraphs covering every edge exactly twice) with `C` one
of its members, then `G` has a cycle cover of length at most `2m - |C|`, `m` the number of
edges of `G`. Written with the subtraction moved to the left (`|C| ≤ m`). -/
theorem lemma_7_2 {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hcubic : G.IsRegularOfDegree 3)
    (C : Finset (Sym2 V)) (hC : IsTwoRegularEdgeSet G C)
    (k : ℕ) (𝒟 : Fin k → Finset (Sym2 V)) (h𝒟 : IsKCDCEven G k 𝒟)
    (i : Fin k) (hi : 𝒟 i = C) :
    ∃ F : Finset (Finset (Sym2 V)), IsCycleCover G F ∧
      coverLength F + C.card ≤ 2 * G.edgeFinset.card := by sorry

end SnarkGen.CycleCover
