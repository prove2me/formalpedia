-- Prove2me | Theorems.Thm_SingleExpBisect_Main_dp_sparse_io_bit_budget
-- name    : SingleExpBisect.Main.dp_sparse_io_bit_budget
-- status  : Proved
-- author  : @Soh Kumabe
-- created : 2026-11-26T15:10:51.512034+00:00
-- url     : https://prove2.me/theorems/99eb7e74-ebfe-4bda-8869-9c47a452556e
-- title:
--   A bit bound for the sparse inputs of Lemmas 3.4–3.6 and the two cut-polynomial outputs
-- statement:
--   Let $G$ have $n$ vertices, let $k$ be the cut parameter, and let $t$ be a node of a rooted tree decomposition satisfying the hypotheses of Section 3. At every child of $t$, supply any sparse list representing its cut polynomial, in any term order. The input word for Lemmas 3.5 and 3.6 consists of the node encoding followed by these child lists. Lemma 3.4 inserts an encoded set $S$ between them. For either input word $x$, one has
--   $$|x|+1\le 64\,2^{64k}(n+1)^{64}.$$
--   Both the full cut polynomial at $t$ and its large-bag truncation, after the prescribed adhesion substitution, admit sparse representations. For every such representation, its encoded output $y$ satisfies the same bound on $|y|+1$. The bound includes the self-delimiting codes of the exponents and rational coefficients, as well as the decomposition and the child identifiers.
-- source:
--   Soh Kumabe, Single-Exponential FPT Algorithms for Minimum Bisection and Matching Cut via a New Unbreakable Decomposition, arXiv:2611.05982, Section 3.3, Lemmas 3.4–3.6. Auxiliary bit-length bound for the published Prove2Me encodings of these dynamic-programming inputs and outputs. https://arxiv.org/abs/2611.05982

import Mathlib
import Definitions.Def_SingleExpBisect_Main_Graphs
import Definitions.Def_SingleExpBisect_Main_Encodings

open scoped Classical
open SingleExpBisect.Main MinBisectFPT ExponomialAssortment.FPTAS

theorem SingleExpBisect.Main.dp_sparse_io_bit_budget {n : ℕ} (G : SimpleGraph (Fin n)) (k : ℕ) (T : RootedTD n)
    (t : Fin T.N) (S : Finset (Fin n)) (Lc : Fin T.N → List ((Var n →₀ ℕ) × ℚ))
    (valid : IsSec3Decomp G T k)
    (children : ∀ s, T.parent s = some t →
      IsSparseRep (Lc s) (fun e => MvPolynomial.coeff e (Zomega G T k s))) :
    (nodeInput G k T t ++ encodeSet S ++ childInput T t Lc).length+1 ≤ stepBound 64 k n ∧
    (nodeInput G k T t ++ childInput T t Lc).length+1 ≤ stepBound 64 k n ∧
    ∀ P : MvPolynomial (Var n) ℚ,
      (P = Zomega G T k t ∨ P = omega (T.adhesion t) (Zle G (T.cone t) (T.bag t) k)) →
      (∃ L, IsSparseRep L (fun e => MvPolynomial.coeff e P)) ∧
      ∀ L : List ((Var n →₀ ℕ) × ℚ), IsSparseRep L (fun e => MvPolynomial.coeff e P) →
        (encodeTerms L).length+1 ≤ stepBound 64 k n := by sorry
