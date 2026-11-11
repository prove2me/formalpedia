-- Prove2me | Theorems.Thm_SatisfiableOrderingCSP_Optimal_theorem_1_3
-- name    : SatisfiableOrderingCSP.Optimal.theorem_1_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T17:47:47.442597+00:00
-- url     : https://prove2.me/theorems/52e8acf5-bfcf-4d57-a4ce-d8e4ed5e652c
-- title:
--   Theorem 1.3 — optimal approximation and conditional hardness
-- statement:
--   Fix a nonempty finite ordering language of nonconstant predicates and any real error epsilon>0. There is one deterministic polynomial-time algorithm for the fixed language and error that, on every completely satisfiable instance, returns an ordering of weighted satisfaction at least alphaLR(language)-epsilon. The mathematical statement retains all strictly positive normalized real constraint weights through an exact-arithmetic RAM guarantee, and separately states polynomial bit time on rational encodings. In addition, assuming the Rich 2-to-1 Games Conjecture, every NP language reduces in deterministic polynomial time to unweighted ordering instances over this language, sending members to value one and nonmembers to value at most alphaLR(language)+epsilon. Constraints may repeat and every scope has distinct arguments. Only the hardness clause assumes the conjecture; neither clause assumes P differs from NP.
--
--   Differences from the source:
--   - encoding: finite indexed sets [n] and positive normalized weighted ordering instances → zero-based Fin indices, indexed repeated constraints, injective scopes, and strictly positive real weights of total one; reason: reindexing changes no instances; isolated variables remain allowed and positive total mass excludes an empty constraint list
--   - encoding: a fixed finite ordering language with nonconstant predicates and the minimum in Definition 4.2 → a nonempty finite set of predicates represented by their nonempty proper sets of satisfying full permutations; reason: every such finite relation is a disjunction of full strict chains; nonemptiness is the meaningful domain of the printed minimum
--   - encoding: maxima over orders and the supremum/minimum in Definition 4.2 → real suprema over finite nonempty permutation sets, a real infimum over eligible local types, and a real supremum over all finite real-coefficient mixtures; reason: scores lie in [0,1], the finite extrema are attained, eligible types exist, and the singleton uniform block gives an admissible mixture
--   - encoding: polynomial-time approximation, including the rational-weight bit-complexity statement in Appendix A.6 → one fixed polynomial-time Turing machine on explicit rational encodings and one fixed rational-constant exact-arithmetic RAM program on real weights; reason: separates bit cost from arithmetic operations while retaining every positive real-weight instance; program and exponent precede the instance
--   - encoding: NP-hardness of distinguishing the printed two threshold predicates for every positive error → the published GapNPHard reduction predicate with concrete encodings, also when the Yes and No thresholds overlap; reason: the prescribed reduction convention imposes no disjointness hypothesis and does not exclude large errors or threshold one
--   - generalization: hardness on instances of CSP(language) → hardness already on unweighted repeated-constraint instances; reason: Theorem 7.1 and the running-time paragraph on printed p. 51 establish this stronger output restriction
-- source:
--   Yury Makarychev (2026), Optimal Approximation Algorithms For Satisfiable Ordering CSPs, held STOC 2027 submission, sha256:e49b7905adb41a36b93abcbd7818d1b18ca86a77dff069da884ba2f8e85775cc, Theorem 1.3, printed p. 5 (PDF p. 8); citation_basis: published.

import Definitions.Def_SatisfiableOrderingCSP_Optimal_RichGames

open scoped BigOperators
open SatisfiableOrderingCSP.Optimal

namespace SatisfiableOrderingCSP.Optimal

theorem theorem_1_3 (Lg : Language) (ε : ℝ) (hε : 0 < ε) :
    (BitApproximation Lg (alphaLR Lg - ε) (fun I => I.value = 1) ∧
      ArithmeticApproximation Lg (alphaLR Lg - ε) (fun I => I.value = 1)) ∧
    (RichGamesConjecture → OrderingGapHard (fun φ => φ ∈ Lg.predicates) (alphaLR Lg + ε)) := by sorry

end SatisfiableOrderingCSP.Optimal
