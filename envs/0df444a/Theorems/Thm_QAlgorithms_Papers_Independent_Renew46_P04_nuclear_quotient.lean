-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P04_nuclear_quotient
-- name    : QAlgorithms.Papers.Independent.Renew46.P04.nuclear_quotient
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T03:52:05.363989+00:00
-- url     : https://prove2.me/theorems/fe4fdf4a-ac2e-4040-ac11-5f85f8046cd6
-- title:
--   §2.2: quotient/range nuclear Banach norm
-- statement:
--   Let $\mathbb K$ be $\mathbb R$ or $\mathbb C$, and let $X,Y$ be Banach spaces over $\mathbb K$. Write $P(X,Y)=X\widehat\otimes_\pi Y$, with its projective norm. A tensor attains this norm when it has a bounded countable pure-tensor representation, convergent with summable norm products, whose cost equals its norm. Write $\mathcal N(X,Y)$ for the range of the canonical map $J:P(X^*,Y)\to\mathcal L(X,Y)$, equipped with the quotient nuclear norm, and $\mathrm{NA}_{\mathcal N}$ for operators having an attaining series in this norm. All duals are continuous linear duals.
--
--   The map induced by $J$ is injective on $Q=P(X^*,Y)/\ker J$ and has image exactly $\mathcal N(X,Y)$. The quotient is complete. For $q\in Q$, let $T=\widetilde Jq$, and let $C_N(T)$ be all its admissible nuclear-series costs. Then $C_N(T)$ is nonempty and bounded below, and
--
--   $$
--   \|q\|=\|T\|_N=\inf C_N(T),\qquad \|T\|_{\mathrm{op}}\le\|T\|_N.
--   $$
--
--   Every such $T$ is compact and, for each $\varepsilon>0$, has a finite-rank operator within $\varepsilon$ in operator norm. The nuclear Banach norm is the actual quotient norm, so its norm axioms are supplied by the constructed quotient rather than assumed.
-- source:
--   Norm-attaining tensors and nuclear operators, arXiv:2006.09871v4, PDF p. 4, §2.2: quotient/range nuclear Banach norm

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

/-- PDF p.4: quotient/range identification, the infimum norm, completeness,
operator-norm domination and finite-rank approximation of every nuclear operator. -/
theorem nuclear_quotient :
    Function.Injective (nuclearOperator : Nuclear K X Y →L[K] (X →L[K] Y)) ∧
    Set.range (nuclearOperator : Nuclear K X Y →L[K] (X →L[K] Y)) =
      (NuclearRange (K := K) (X := X) (Y := Y) : Set (X →L[K] Y)) ∧
    CompleteSpace (Nuclear K X Y) ∧
    (∀ T : Nuclear K X Y, (nuclearCosts (nuclearOperator T)).Nonempty ∧
      BddBelow (nuclearCosts (nuclearOperator T)) ∧ ‖T‖ = sInf (nuclearCosts (nuclearOperator T)) ∧
      ‖nuclearOperator T‖ ≤ ‖T‖ ∧ IsCompactOperator (nuclearOperator T) ∧
      ∀ eps : ℝ, 0 < eps → ∃ S : X →L[K] Y,
        FiniteDimensional K S.range ∧ ‖nuclearOperator T - S‖ < eps) := by sorry

end Banach

end QAlgorithms.Papers.Independent.Renew46.P04

end
