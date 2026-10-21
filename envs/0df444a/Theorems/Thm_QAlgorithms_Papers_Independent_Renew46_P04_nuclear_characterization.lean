-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P04_nuclear_characterization
-- name    : QAlgorithms.Papers.Independent.Renew46.P04.nuclear_characterization
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T03:54:59.686518+00:00
-- url     : https://prove2.me/theorems/24f47c80-92c8-4e8d-8e28-0df35c394243
-- title:
--   Theorem 3.2: nuclear representation characterization
-- statement:
--   Let $\mathbb K$ be $\mathbb R$ or $\mathbb C$, and let $X,Y$ be Banach spaces over $\mathbb K$. Write $P(X,Y)=X\widehat\otimes_\pi Y$, with its projective norm. A tensor attains this norm when it has a bounded countable pure-tensor representation, convergent with summable norm products, whose cost equals its norm. Write $\mathcal N(X,Y)$ for the range of the canonical map $J:P(X^*,Y)\to\mathcal L(X,Y)$, equipped with the quotient nuclear norm, and $\mathrm{NA}_{\mathcal N}$ for operators having an attaining series in this norm. All duals are continuous linear duals.
--
--   Fix a nuclear operator $T=\sum_na_nf_n\otimes y_n$, with positive summable real $a_n$, unit $f_n\in X^*$ and unit $y_n\in Y$, the operator series converging at every input. For the quotient pullback $q^*H\in(\ker J)^\perp$, the three conditions are equivalent:
--
--   $$
--   \|T\|_N=\sum_na_n;\qquad \exists H\in S_{\mathcal N(X,Y)^*}\ \forall n,\ q^*H(f_n\otimes y_n)=1;\qquad \forall H\in S_{\mathcal N(X,Y)^*},\ H(T)=\|T\|_N\Rightarrow\forall n,\ q^*H(f_n\otimes y_n)=1.
--   $$
--
--   An optimal such representation implies nuclear norm attainment. The printed $x_n\in S_X$ is corrected to the dual factor required by the series and proof; the preceding dual isometry makes this exactly the annihilator formulation in the source.
-- source:
--   Norm-attaining tensors and nuclear operators, arXiv:2006.09871v4, PDF p. 7, Theorem 3.2: nuclear representation characterization

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

/-- PDF p.7, Theorem 3.2: x_n in S_X is corrected to f_n in S_(X*), as the series and proof require.
G(T) is quotient evaluation, without assuming an optimal tensor lift.
As in Theorem 3.1, the printed parenthetical membership is a consequence of this
representation being optimal, not a converse for arbitrary representations. -/
theorem nuclear_characterization (T : Nuclear K X Y) (a : ℕ → ℝ)
    (f : ℕ → (X →L[K] K)) (y : ℕ → Y) (ha : ∀ n, 0 < a n) (hs : Summable a)
    (hu : ∀ n, ‖f n‖ = 1 ∧ ‖y n‖ = 1)
    (hT : ∀ x, HasSum (fun n => (a n : K) • ((f n x) • y n)) (nuclearOperator T x)) :
    ((‖T‖ = ∑' n, a n) ↔ ∃ H : Nuclear K X Y →L[K] K,
      ‖H‖ = 1 ∧ ∀ n, pullNuclearDual H (pure (f n) (y n)) = 1) ∧
    ((‖T‖ = ∑' n, a n) ↔ ∀ H : Nuclear K X Y →L[K] K,
      ‖H‖ = 1 → H T = (‖T‖ : K) → ∀ n, pullNuclearDual H (pure (f n) (y n)) = 1) ∧
    ((‖T‖ = ∑' n, a n) → NuclearAttains T) := by sorry

end Banach

end QAlgorithms.Papers.Independent.Renew46.P04

end
