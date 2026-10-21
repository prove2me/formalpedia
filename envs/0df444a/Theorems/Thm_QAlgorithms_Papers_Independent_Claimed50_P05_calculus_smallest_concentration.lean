-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P05_calculus_smallest_concentration
-- name    : QAlgorithms.Papers.Independent.Claimed50.P05.calculus_smallest_concentration
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T09:08:20.945354+00:00
-- url     : https://prove2.me/theorems/5a5aa2c6-9b95-4938-b138-988d97047ab3
-- title:
--   Corollary 4.3
-- statement:
--   Let $k$ be $\mathbb R$ or $\mathbb C$, let $H$ be a Hilbert space, and let $(X,\Sigma)$ be a measurable space. Write $M(X)$ for the finite $k$-valued measurable functions with pointwise equality, and $M_b(X)$ for its bounded functions. Let $\Phi:M(X)\to C(H)$ satisfy axioms MFC1–MFC5, where $C(H)$ consists of closed functional linear graphs. All operator equalities include equality of domains; an overline on an operator denotes graph closure.
--
--   Suppose $X=k$ with its Borel sigma algebra, let $z(t)=t$, and set $A=\Phi(z)$. Then
--
--   $$\Phi\text{ is concentrated on }\sigma(A),\qquad\sigma(A)\subseteq F\quad\text{for every closed concentration set }F\subseteq k.$$
--
--   Thus the spectrum is the smallest closed set on which the calculus is concentrated.
--
--   This gives the precise minimal closed concentration statement.
-- source:
--   The Functional Calculus Approach to the Spectral Theorem, arXiv:2003.06130v2, PDF p. 17, Corollary 4.3

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

/-- Corollary 4.3, PDF p.17: spectrum is the smallest closed concentration set. -/
theorem calculus_smallest_concentration (F : Symbol k k → Relation H) (hF : Calculus F) :
    Concentrated F (spectrumOf (k := k) (F scalarIdentity)) ∧
    ∀ S : Set k, IsClosed S → Concentrated F S → spectrumOf (k := k) (F scalarIdentity) ⊆ S := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P05

end
