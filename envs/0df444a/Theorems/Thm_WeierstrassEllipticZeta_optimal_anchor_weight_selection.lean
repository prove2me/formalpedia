-- Prove2me | Theorems.Thm_WeierstrassEllipticZeta_optimal_anchor_weight_selection
-- name    : WeierstrassEllipticZeta.optimal_anchor_weight_selection
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-22T18:42:18.8614+00:00
-- url     : https://prove2.me/theorems/fa592e2a-353c-4ff0-98a2-6db3aabc419e
-- title:
--   Attained optimal anchor weight and exact scalar budget criterion
-- statement:
--   For the existing sparse-GCD anchor candidates, let k(a) be the number of classes of X modulo the candidate's period kernel and let d(a) be its additive degree. A point has d(a)=m and weight w(a)=k(a)=|X|. A line or whole fibre has d(a)=0 and weight w(a)=(m+1)*k(a).
--
--   The theorem proves that the minimum weight W is attained by the chosen optimalSparseAnchor, is at most |X|, is at least 1 if X is nonempty, and is no larger than any anchor's weight. Every minimizing anchor with d(a)=0 satisfies
--
--   k(a) <= floor(|X|/(m+1)).
--
--   Moreover, for every natural-number local cost E and real constant C, existence of an anchor satisfying
--
--   k(a)*E <= C*(d(a)+1)*n^2
--
--   is equivalent to the single scalar inequality
--
--   W*E <= C*(m+1)*n^2.
--
--   The same minimum and chosen minimizer work for all E and C. The result requires no analytic, nonvanishing or homogeneity hypotheses beyond the existing definitions; empty X and zero degrees are allowed, with the lower bound on W conditional on X being nonempty.
--
--   The new cutoff restricts optimal zero-additive-degree candidates, not all valid lines or fibres. Previously every quotient class count was only trivially bounded by |X|; an optimal nonpoint choice must now have at most floor(|X|/(m+1)) classes. This is a pruning criterion and exact budget reformulation. Feasibility and the minimum remain classical, and the theorem does not prove the uniform geometric estimate or change the integer-search bound.
-- source:
--   Derived optimum-weight criterion for the A.1 frontier https://prove2.me/theorems/7e7bb591-b0c3-4c9f-a487-565853b9f422. A point has weight |X|; a nonpoint with k quotient classes has weight (m+1)*k. The least attained natural-number weight W exists, is at most |X|, and is positive for nonempty X. The same minimizing anchor works for all natural local costs E and real C, and existence of an old anchor budget is equivalent to W*E<=C*(m+1)*n^2. Every minimizing zero-additive-degree candidate has k<=floor(|X|/(m+1)). Primary pinned sources: Nat.find_spec and Nat.find_min', https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Data/Nat/Find.lean; finite image cardinality, https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Data/Finset/Card.lean; quotient equality, https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/LinearAlgebra/Quotient/Basic.lean. This is a derived optimization lemma, not the uniform geometric bound. Mission context: Appendix A of Senthil Kumar K (2026), https://www.cambridge.org/core/journals/proceedings-of-the-edinburgh-mathematical-society/article/algebraic-independence-of-values-of-weierstrass-elliptic-and-zeta-functions/E91A8EEEB1F63536D95D1DE7D7DD47E2#app1. Coordinate feasibility remains classical. The same C, chart point and local cost are preserved; individual anchor coordinates, degrees and class counts may change. The integer-search and existing slice-count bounds are unchanged.

import Definitions.Def_WeierstrassEllipticZeta_OptimalAnchorWeight
import Mathlib.Tactic

noncomputable section
open scoped Classical
open WeierstrassEllipticZeta

theorem WeierstrassEllipticZeta.optimal_anchor_weight_selection
    (Λ : Submodule ℤ ℂ) (η : Λ →ₗ[ℤ] ℂ)
    (X : Finset ℂ) (S : Fin 5 → ℂ → ℂ) (Q : MvPolynomial (Fin 7) ℂ)
    (m n : ℕ) (K : Set ℂ) (Z : Finset ℂ) :
    (minimumAnchorWeight Λ η X S Q m n K Z ≤ X.card ∧
      (X.Nonempty → 1 ≤ minimumAnchorWeight Λ η X S Q m n K Z) ∧
      sparseAnchorWeight Λ η X S Q m n K Z
        (optimalSparseAnchor Λ η X S Q m n K Z) =
          minimumAnchorWeight Λ η X S Q m n K Z ∧
      (∀ a : SparseGCDAnchorCandidate Λ η X S Q m n K Z,
        minimumAnchorWeight Λ η X S Q m n K Z ≤
          sparseAnchorWeight Λ η X S Q m n K Z a) ∧
      (∀ a : SparseGCDAnchorCandidate Λ η X S Q m n K Z,
        sparseAnchorWeight Λ η X S Q m n K Z a =
          minimumAnchorWeight Λ η X S Q m n K Z →
        elementaryDegree (candidateLocusShape Λ η X
          (sparseGCDAnchorLocus Λ η X S Q m n K Z a)) m = 0 →
        candidateClassCount Λ η X (sparseGCDAnchorLocus Λ η X S Q m n K Z a) ≤
          X.card / (m + 1))) ∧
    ∀ (E : ℕ) (C : ℝ),
      (∃ a : SparseGCDAnchorCandidate Λ η X S Q m n K Z,
        (((X.image (elementaryPeriodKernel Λ η (candidateLocusShape Λ η X
          (sparseGCDAnchorLocus Λ η X S Q m n K Z a))).mkQ).card * E : ℕ) : ℝ) ≤
          C * (((elementaryDegree (candidateLocusShape Λ η X
            (sparseGCDAnchorLocus Λ η X S Q m n K Z a)) m + 1) * n ^ 2 : ℕ) : ℝ)) ↔
      (((minimumAnchorWeight Λ η X S Q m n K Z * E : ℕ) : ℝ) ≤
        C * (((m + 1) * n ^ 2 : ℕ) : ℝ)) := by sorry
