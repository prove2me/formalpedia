-- Prove2me | Theorems.Thm_QuantumBipartiteTesting_Bipartiteness_local_oracle_algorithm_compilation
-- name    : QuantumBipartiteTesting.Bipartiteness.local_oracle_algorithm_compilation
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T16:35:07.469751+00:00
-- url     : https://prove2.me/theorems/a6acbcb2-2232-47c7-b81a-dd2cf504fb82
-- title:
--   Exact compilation of locally simulated quantum query algorithms
-- statement:
--   Let $I$ and $L$ be finite sets of source and logical query addresses. Fix a source address $i_0$, three source addresses $a(l,0),a(l,1),a(l,2)$ for each logical address $l$, and a function $g$ mapping their binary answers to a logical binary answer. All of this data is independent of the input function $f$.
--
--   For every $q$-query logical quantum algorithm with finite workspace and a computational-basis Boolean output event, there is a source quantum algorithm, also with finite workspace, whose query count satisfies
--
--   $$q_S\leq 6q,$$
--
--   and whose acceptance probability on every source function $f$ equals that of the logical algorithm with oracle
--
--   $$l\longmapsto g(l,f(a(l,0)),f(a(l,1)),f(a(l,2))).$$
--
--   Both answer registers are full bit-string spaces, including unused encodings. The result applies the constant-query oracle reduction to arbitrary unitary interlayers and arbitrary initial unit vectors.
-- source:
--   Kayal–Sen–Szabó, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/878.pdf, §2.1.2 p. 8 and Lemma 3.16 proof p. 21. Generic circuit-composition interface for an explicit clean six-query implementation of the stated O(1) simulation.

import Definitions.Def_QuantumBipartiteTesting_Bipartiteness_Reduction
open QuantumBipartiteTesting.Bipartiteness

theorem QuantumBipartiteTesting.Bipartiteness.local_oracle_algorithm_compilation {I L : Type} [Fintype I] [Fintype L] [DecidableEq I] [DecidableEq L]
    (kS kT w q : ℕ) (i0 : I) (a : L→Fin 3→I)
    (g : L→(Fin 3→Bits kS)→Bits kT) (A : Algorithm L kT w q)
    (out : ((L×Bits kT)×Fin w)→Bool) :
    ∃ wS qS : ℕ, ∃ A' : Algorithm I kS wS qS,
    ∃ out' : ((I×Bits kS)×Fin wS)→Bool, qS ≤ 6*q ∧ ∀ f : I→Bits kS,
      A'.outputProb (QAlgorithms.xorOracle f) out' true =
        A.outputProb (QAlgorithms.xorOracle (fun l => g l (fun j => f (a l j)))) out true := by sorry
