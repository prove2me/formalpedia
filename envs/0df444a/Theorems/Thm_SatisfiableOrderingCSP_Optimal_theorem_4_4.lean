-- Prove2me | Theorems.Thm_SatisfiableOrderingCSP_Optimal_theorem_4_4
-- name    : SatisfiableOrderingCSP.Optimal.theorem_4_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T17:47:37.425515+00:00
-- url     : https://prove2.me/theorems/68d29fa2-fcd5-4928-81de-7477924fc25d
-- title:
--   Theorem 4.4 — computing and applying the approximation scheme
-- statement:
--   There is one finite rational-constant arithmetic program which, for every encoded finite ordering language and every real epsilon>0, terminates and outputs a rational number within epsilon of alphaLR and an explicitly encoded finite rational IDU-plus mixture with guarantee at least alphaLR-epsilon. Preprocessing depends only on the language and error. For each such returned mixture there is a fixed random word program, using unit-cost uniform finite sampling and polynomially bounded words, that on every canonically feasible instance returns exactly the mixture's distribution on some valid pair of canonical orders in C(n+m+1) steps. On every valid pair of relaxed orders its expected weighted satisfaction is at least alphaLR-epsilon, for all positive real weights. There are deterministic polynomial-time implementations with the same guarantee, in bit time for rational inputs and arithmetic operations for arbitrary real weights. This states the computational guarantees of the source; conditional expectation is the source's method of realizing the deterministic implementation.
--
--   Differences from the source:
--   - encoding: finite indexed sets [n] and positive normalized weighted ordering instances → zero-based Fin indices, indexed repeated constraints, injective scopes, and strictly positive real weights of total one; reason: reindexing changes no instances; isolated variables remain allowed and positive total mass excludes an empty constraint list
--   - encoding: a fixed finite ordering language with nonconstant predicates and the minimum in Definition 4.2 → a nonempty finite set of predicates represented by their nonempty proper sets of satisfying full permutations; reason: every such finite relation is a disjunction of full strict chains; nonemptiness is the meaningful domain of the printed minimum
--   - encoding: maxima over orders and the supremum/minimum in Definition 4.2 → real suprema over finite nonempty permutation sets, a real infimum over eligible local types, and a real supremum over all finite real-coefficient mixtures; reason: scores lie in [0,1], the finite extrema are attained, eligible types exist, and the singleton uniform block gives an admissible mixture
--   - encoding: polynomial-time approximation, including the rational-weight bit-complexity statement in Appendix A.6 → one fixed polynomial-time Turing machine on explicit rational encodings and one fixed rational-constant exact-arithmetic RAM program on real weights; reason: separates bit cost from arithmetic operations while retaining every positive real-weight instance; program and exponent precede the instance
--   - encoding: randomized linear-time application and preprocessing of a finite rational scheme → an explicit finite word program with unit-cost uniform finite sampling and a terminating rational-constant RAM preprocessor taking a real tolerance; reason: scans, indexed updates, and shuffles are counted primitive operations; fixed rational coin sampling would instead have expected constant bit cost
-- source:
--   Yury Makarychev (2026), Optimal Approximation Algorithms For Satisfiable Ordering CSPs, held STOC 2027 submission, sha256:e49b7905adb41a36b93abcbd7818d1b18ca86a77dff069da884ba2f8e85775cc, Theorem 4.4, printed p. 18 (PDF p. 21); citation_basis: published.

import Definitions.Def_SatisfiableOrderingCSP_Optimal_Effectivity

open scoped BigOperators
open SatisfiableOrderingCSP.Optimal

namespace SatisfiableOrderingCSP.Optimal

theorem theorem_4_4 :
    ∃ P : NearLinearRSP.TwoResources.Program, ArithmeticProgram P ∧
      ∀ (Lg : Language) (code : List Bool), Lg.Encoding code →
        ∀ ε : ℝ, 0 < ε → ∃ (t : ℕ) (s : NearLinearRSP.TwoResources.RAMState) (a : ℚ) (ν : RationalMixture),
          NearLinearRSP.TwoResources.Execution P (SchemeInput code ε)
            NearLinearRSP.TwoResources.initialState s t ∧
          OutputBits s (encodeRat a ++ ν.encode) ∧
          |(a : ℝ) - alphaLR Lg| ≤ ε ∧
          alphaLR Lg - ε ≤ ν.mixture.guarantee Lg ∧
          LinearMixtureImplementation Lg ν.mixture ∧
          (∀ (I : Instance), I.Over Lg → ∀ L R, I.RelaxedOrders L R →
            alphaLR Lg - ε ≤ ∑ σ : Order I.n, ν.mixture.law L R σ * I.score σ) ∧
          BitApproximation Lg (alphaLR Lg - ε) Instance.CanonicallyFeasible ∧
          ArithmeticApproximation Lg (alphaLR Lg - ε) Instance.CanonicallyFeasible := by sorry

end SatisfiableOrderingCSP.Optimal
