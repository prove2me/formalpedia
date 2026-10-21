-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P04_tensor_characterization
-- name    : QAlgorithms.Papers.Independent.Renew46.P04.tensor_characterization
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T03:54:30.319+00:00
-- url     : https://prove2.me/theorems/1e2093b1-f034-411e-95e5-df7f184b5d3c
-- title:
--   Theorem 3.1: tensor representation characterization
-- statement:
--   Let $\mathbb K$ be $\mathbb R$ or $\mathbb C$, and let $X,Y$ be Banach spaces over $\mathbb K$. Write $P(X,Y)=X\widehat\otimes_\pi Y$, with its projective norm. A tensor attains this norm when it has a bounded countable pure-tensor representation, convergent with summable norm products, whose cost equals its norm. Write $\mathcal N(X,Y)$ for the range of the canonical map $J:P(X^*,Y)\to\mathcal L(X,Y)$, equipped with the quotient nuclear norm, and $\mathrm{NA}_{\mathcal N}$ for operators having an attaining series in this norm. All duals are continuous linear duals.
--
--   Fix $z=\sum_na_nx_n\otimes y_n$, with convergence in projective norm, strictly positive summable real $a_n$, and $\|x_n\|=\|y_n\|=1$. The following three conditions are equivalent:
--
--   $$
--   \|z\|_\pi=\sum_na_n;\qquad \exists G\in S_{\mathcal B(X\times Y)}\ \forall n,\ G(x_n,y_n)=1;\qquad \forall G\in S_{\mathcal B(X\times Y)},\ \widetilde G(z)=\|z\|_\pi\Rightarrow\forall n,\ G(x_n,y_n)=1.
--   $$
--
--   Optimality of this representation implies tensor norm attainment. The equalities are scalar equalities to $1$, including in the complex case; membership in the attaining set is not claimed equivalent to optimality of every chosen representation.
-- source:
--   Norm-attaining tensors and nuclear operators, arXiv:2006.09871v4, PDF p. 6, Theorem 3.1: tensor representation characterization

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

/-- PDF p.6, Theorem 3.1: equivalence for this fixed strictly positive representation.
The printed parenthetical membership is retained only as a consequence: existence
of an optimal representation does not make every chosen representation optimal. -/
theorem tensor_characterization [CompleteSpace X] [CompleteSpace Y] (z : Projective K X Y) (a : ℕ → ℝ) (x : ℕ → X) (y : ℕ → Y)
    (ha : ∀ n, 0 < a n) (hs : Summable a) (hu : ∀ n, ‖x n‖ = 1 ∧ ‖y n‖ = 1)
    (hz : HasSum (fun n => (a n : K) • pure (x n) (y n)) z) :
    ((‖z‖ = ∑' n, a n) ↔ ∃ G : Bilinear K X Y K,
      ‖G‖ = 1 ∧ ∀ n, G (pair (x n) (y n)) = 1) ∧
    ((‖z‖ = ∑' n, a n) ↔ ∀ G : Bilinear K X Y K,
      ‖G‖ = 1 → extendBilinear G z = (‖z‖ : K) →
        ∀ n, G (pair (x n) (y n)) = 1) ∧
    ((‖z‖ = ∑' n, a n) → TensorAttains z) := by sorry

end Banach

end QAlgorithms.Papers.Independent.Renew46.P04

end
