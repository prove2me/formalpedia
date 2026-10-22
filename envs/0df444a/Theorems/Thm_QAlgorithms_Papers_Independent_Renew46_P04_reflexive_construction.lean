-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P04_reflexive_construction
-- name    : QAlgorithms.Papers.Independent.Renew46.P04.reflexive_construction
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T03:55:32.214741+00:00
-- url     : https://prove2.me/theorems/5a14867d-9e9b-4a19-8504-c7f15ac6c949
-- title:
--   Example 3.3: reflexive-space construction
-- statement:
--   Let $\mathbb K$ be $\mathbb R$ or $\mathbb C$, and let $X,Y$ be Banach spaces over $\mathbb K$. Write $P(X,Y)=X\widehat\otimes_\pi Y$, with its projective norm. A tensor attains this norm when it has a bounded countable pure-tensor representation, convergent with summable norm products, whose cost equals its norm. Write $\mathcal N(X,Y)$ for the range of the canonical map $J:P(X^*,Y)\to\mathcal L(X,Y)$, equipped with the quotient nuclear norm, and $\mathrm{NA}_{\mathcal N}$ for operators having an attaining series in this norm. All duals are continuous linear duals.
--
--   Assume $X,Y$ are reflexive and either $X^*$ or $Y$ has the approximation property. Fix a linear isometry $G:X^*\to Y^*$ and a sequence $f_n\in S_{X^*}$. There are vectors $y_n\in S_Y$ with $G(f_n)(y_n)=1$, chosen before the coefficients, such that every summable sequence $0<a_n\le1$ defines an attaining nuclear operator satisfying
--
--   $$
--   T(x)=\sum_na_nf_n(x)y_n,\qquad T\in\mathrm{NA}_{\mathcal N}(X,Y),\qquad \|T\|_N=\sum_na_n.
--   $$
--
--   This constructs nuclear norm attaining operators from the specified isometry and its norming vectors. Reflexivity is expressed by surjectivity of the canonical bidual inclusion.
-- source:
--   Norm-attaining tensors and nuclear operators, arXiv:2006.09871v4, PDF p. 7, Example 3.3: reflexive-space construction

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P04

noncomputable section

set_option synthInstance.maxSize 8192

namespace QAlgorithms.Papers.Independent.Renew46.P04

open Filter Set

open scoped Topology TensorProduct ENNReal

universe u v

variable {K : Type*} [RCLike K]

attribute [local instance] QAlgorithms.Papers.Independent.Renew46.P04.linearOperatorNorm

attribute [local instance] QAlgorithms.Papers.Independent.Renew46.P04.linearOperatorSeminormedGroup

attribute [local instance] QAlgorithms.Papers.Independent.Renew46.P04.linearOperatorNormedGroup

attribute [local instance] QAlgorithms.Papers.Independent.Renew46.P04.linearOperatorNormedSpace

attribute [local instance] QAlgorithms.Papers.Independent.Renew46.P04.dualNormedGroup

attribute [local instance] QAlgorithms.Papers.Independent.Renew46.P04.dualNormedSpace

section Banach

variable {X Y Z : Type*}

variable [NormedAddCommGroup X] [NormedSpace K X] [CompleteSpace X]

variable [NormedAddCommGroup Y] [NormedSpace K Y] [CompleteSpace Y]

variable [NormedAddCommGroup Z] [NormedSpace K Z] [CompleteSpace Z]

/-- PDF p.7, Example 3.3: the vectors in Y are chosen to norm the specified isometry. -/
theorem reflexive_construction
    (hX : Function.Surjective (NormedSpace.inclusionInDoubleDual K X))
    (hY : Function.Surjective (NormedSpace.inclusionInDoubleDual K Y))
    (hAP : ApproximationProperty K (X →L[K] K) ∨ ApproximationProperty K Y)
    (G : (X →L[K] K) →ₗᵢ[K] (Y →L[K] K))
    (f : ℕ → (X →L[K] K)) (hf : ∀ n, ‖f n‖ = 1) :
    ∃ y : ℕ → Y, (∀ n, ‖y n‖ = 1 ∧ G (f n) (y n) = 1) ∧
      ∀ a : ℕ → ℝ, (∀ n, 0 < a n ∧ a n ≤ 1) → Summable a →
        ∃ T : Nuclear K X Y, NuclearAttains T ∧ ‖T‖ = ∑' n, a n ∧
          ∀ x, HasSum (fun n => (a n : K) • ((f n x) • y n)) (nuclearOperator T x) := by sorry

end Banach

end QAlgorithms.Papers.Independent.Renew46.P04

end
