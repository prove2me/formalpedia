-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P05_calculus_pullback
-- name    : QAlgorithms.Papers.Independent.Claimed50.P05.calculus_pullback
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T09:03:36.673977+00:00
-- url     : https://prove2.me/theorems/6cc88e96-3e34-4853-b172-d46f022a2569
-- title:
--   Proposition 2.7
-- statement:
--   Let $k$ be $\mathbb R$ or $\mathbb C$, let $H$ be a Hilbert space, and let $(X,\Sigma)$ be a measurable space. Write $M(X)$ for the finite $k$-valued measurable functions with pointwise equality, and $M_b(X)$ for its bounded functions. Let $\Phi:M(X)\to C(H)$ satisfy axioms MFC1–MFC5, where $C(H)$ consists of closed functional linear graphs. All operator equalities include equality of domains; an overline on an operator denotes graph closure.
--
--   Let $(Y,\Sigma_Y)$ be another measurable space and let $T:M(Y)\to M(X)$ be a unital $k$-linear star homomorphism. Suppose $f_n\to f$ boundedly and pointwise implies $Tf_n\to Tf$ boundedly and pointwise. Then
--
--   $$(T^*\Phi)(f):=\Phi(Tf)$$
--
--   is a measurable functional calculus on $Y$.
--
--   This transports a calculus through a homomorphism of symbol algebras.
-- source:
--   The Functional Calculus Approach to the Spectral Theorem, arXiv:2003.06130v2, PDF p. 12, Proposition 2.7

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P05

noncomputable section

attribute [local instance] Classical.propDecidable

open Set Filter MeasureTheory

open scoped Topology ENNReal InnerProductSpace

namespace QAlgorithms.Papers.Independent.Claimed50.P05

universe u v w

variable {k : Type*} [RCLike k]

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace k H]
  [CompleteSpace H] [NormedAddCommGroup K] [InnerProductSpace k K] [CompleteSpace K]

/-- Proposition 2.7, PDF p.12: pull-back by a unital star homomorphism preserving bp convergence.
Source correction (independently audited in moderation round 1).
Printed: Proposition 2.7 says star-homomorphism without explicitly saying unital.
Changed: Require a unital scalar-preserving star homomorphism of the symbol algebras.
Why: MFC1 for the pull-back requires preservation of 1. The zero homomorphism otherwise contradicts the conclusion on a nonzero Hilbert space. Scalar preservation is the standing K-algebra homomorphism convention.
-/
theorem calculus_pullback (F : Symbol X k → Relation H) (hF : Calculus F)
    (T : Symbol Y k → Symbol X k) (hT : SymbolHom T)
    (hbp : ∀ fn f, BP fn f → BP (fun n => T (fn n)) (T f)) :
    Calculus (fun f => F (T f)) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P05

end
