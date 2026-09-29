-- Prove2me | Theorems.Thm_WeierstrassCurve_exists_enum_cyclicKernels_veluQuotient_discriminant_ne_zero
-- name    : WeierstrassCurve.exists_enum_cyclicKernels_veluQuotient_discriminant_ne_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.681435+00:00
-- url     : https://prove2.me/theorems/38c69004-ff10-5df1-acd3-18b5038d52f0
-- title:
--   Enumeration of the ℓ+1 cyclic kernels with nonsingular Vélu quotients
-- statement:
--   Let $K$ be an algebraically closed field equipped with decidable equality, let $\ell$ be a prime (given as a `Fact`) with $\ell \neq 2$ and with $\ell \neq 0$ in $K$, and let $W$ be a Weierstrass curve over $K$ that is elliptic. Then there exist a type $\iota$ and a `Fintype` structure on it with $\#\iota = \ell + 1$, together with a family $Q : \iota \to W(K)$ of points of the affine model of $W$, such that: each $Q_i$ has additive order exactly $\ell$; the map sending $i$ to the subgroup $\mathbb{Z}\cdot Q_i$ of integer multiples of $Q_i$ is injective; and for each $i$ the Weierstrass curve `W.veluQuotient (W.oddOrderSummingSet (Q i) (ℓ / 2))` has nonzero discriminant $\Delta$. Here `W.oddOrderSummingSet (Q i) (ℓ / 2)` is the finite subset of $K \times K$ consisting of the coordinates of the points $k \cdot Q_i$ for $1 \le k \le \lfloor \ell/2 \rfloor$, with the point at infinity recorded as $(0,0)$, and for a finite set $S \subseteq K \times K$ the curve `W.veluQuotient S` has the same $a_1, a_2, a_3$ as $W$, while $a_4$ is replaced by $a_4 - 5\sum_{P \in S} t(P)$ and $a_6$ by $a_6 - b_2 \sum_{P \in S} t(P) - 7 \sum_{P \in S} w(P)$ in Vélu's notation.
--
--   This packages the input data of the modular equation $\Phi_\ell(j(E), Y) = \prod_i (Y - j(E/C_i))$: an index set of size $\ell+1$ for the cyclic subgroups of order $\ell$ of an elliptic curve over an algebraically closed field in which $\ell$ is invertible, each given by a generator, together with the nonsingularity of the corresponding curve produced by Vélu's formulas. It is used by [`WeierstrassCurve.bijOn_cyclicQuotientJ_isRoot_modularPolynomial_of_transcendental_j`](thm.html#WeierstrassCurve.bijOn_cyclicQuotientJ_isRoot_modularPolynomial_of_transcendental_j).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_exists_enum_cyclicKernels_veluQuotient_discriminant_ne_zero.lean

import Mathlib
import Definitions.Def_WeierstrassCurve_Velu
import Definitions.Def_WeierstrassCurve_OddOrderSummingSet

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open WeierstrassCurve WeierstrassCurve.Affine

theorem WeierstrassCurve.exists_enum_cyclicKernels_veluQuotient_discriminant_ne_zero
    {K : Type*} [Field K] [IsAlgClosed K] [DecidableEq K]
    {ℓ : ℕ} [Fact ℓ.Prime] (hℓ2 : ℓ ≠ 2) (hℓK : (ℓ : K) ≠ 0)
    (W : WeierstrassCurve K) [W.IsElliptic] :
    ∃ (ι : Type) (_ : Fintype ι), Fintype.card ι = ℓ + 1 ∧
      ∃ Q : ι → W.toAffine.Point, (∀ i, addOrderOf (Q i) = ℓ) ∧
        (Function.Injective fun i => AddSubgroup.zmultiples (Q i)) ∧
        ∀ i, (W.veluQuotient (W.oddOrderSummingSet (Q i) (ℓ / 2))).Δ ≠ 0 := by sorry
