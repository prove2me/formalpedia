-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P15_lemma7_relativeDistanceContinuity
-- name    : QAlgorithms.Papers.Independent.Dependency50.P15.lemma7_relativeDistanceContinuity
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T16:24:48.115676+00:00
-- url     : https://prove2.me/theorems/9359a187-292a-4b6d-8fea-34fed11ab16d
-- title:
--   Lemma 7: continuity of relative entropy distance to a convex operator set
-- statement:
--   Let $A$ be a nonzero finite-dimensional complex Hilbert space and let $C$ be a closed, convex, bounded set of positive semidefinite operators containing a positive definite operator. Members of $C$ need not have trace one. For each density state $\tau$, define $D_C(\tau)=\inf_{\gamma\in C}D(\tau\|\gamma)$, with $D(\tau\|\gamma)=\operatorname{Tr}\tau(\log_2\tau-\log_2\gamma)$ and value $+\infty$ on support failure. This infimum is finite and attained. Its variation set over pairs of states is nonempty and bounded above; let $\kappa$ be its supremum.
--
--   For all density states $\rho,\sigma$ and every $\varepsilon\ge0$ with $\frac12\|\rho-\sigma\|_1\le\varepsilon$,
--
--   $$|D_C(\rho)-D_C(\sigma)|\le\varepsilon\kappa+(1+\varepsilon)h_2\!\left(\frac{\varepsilon}{1+\varepsilon}\right).$$
--
--   This controls relative entropy distance to general convex operator sets. Negative distance values are retained; no normalization of the comparison operators is imposed.
-- source:
--   Tight uniform continuity bounds for quantum entropies: conditional entropy, relative entropy distance and energy constraints, arXiv:1507.07775v6, PDF p. 5, Lemma 7: continuity of relative entropy distance to a convex operator set

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P15

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder Matrix.Norms.L2Operator

attribute [local instance] Classical.propDecidable Classical.decEq

namespace QAlgorithms.Papers.Independent.Dependency50.P15

open QAlgorithms.Papers.Independent.Information100.P08 (bellVector)

/-- Lemma 7, PDF pp.5–6, Eq.(7): the operator set need not be normalized.
Its extended-real distance is attained and finite, and its actual variation is finite.
These conclusions guard all real projections and suprema used in the continuity bound. -/
theorem lemma7_relativeDistanceContinuity {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
    (C : Set (Matrix I I ℂ)) (hclosed : IsClosed C) (hconvex : Convex ℝ C)
    (hbounded : Bornology.IsBounded C) (hpositive : ∀ gamma ∈ C, gamma.PosSemidef)
    (hfull : ∃ gamma ∈ C, gamma.PosDef)
    (rho sigma : Matrix I I ℂ) (hrho : IsDensityMatrix rho) (hsigma : IsDensityMatrix sigma)
    (epsilon : ℝ) (hepsilon : 0 ≤ epsilon) (hclose : traceDistance rho sigma ≤ epsilon) :
    (∀ tau : Matrix I I ℂ, IsDensityMatrix tau →
      relativeDistance C tau ≠ ⊥ ∧ relativeDistance C tau ≠ ⊤ ∧
      ∃ gamma ∈ C, positiveOperatorRelativeEntropyBits tau gamma = relativeDistance C tau) ∧
    (relativeVariations C).Nonempty ∧ BddAbove (relativeVariations C) ∧
    |relativeDistanceValue C rho - relativeDistanceValue C sigma| ≤
      epsilon * relativeVariation C + (1 + epsilon) * binEntropy2 (epsilon / (1 + epsilon)) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P15

end
