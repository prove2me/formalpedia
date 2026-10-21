-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P05_calculus_unitary_transport
-- name    : QAlgorithms.Papers.Independent.Claimed50.P05.calculus_unitary_transport
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T09:21:41.389477+00:00
-- url     : https://prove2.me/theorems/0d59e82c-5fed-4852-b20c-9046ee6b2c57
-- title:
--   §2.6, unnumbered: unitary transport
-- statement:
--   Let $k$ be $\mathbb R$ or $\mathbb C$, let $H$ be a Hilbert space, and let $(X,\Sigma)$ be a measurable space. Write $M(X)$ for the finite $k$-valued measurable functions with pointwise equality, and $M_b(X)$ for its bounded functions. Let $\Phi:M(X)\to C(H)$ satisfy axioms MFC1–MFC5, where $C(H)$ consists of closed functional linear graphs. All operator equalities include equality of domains; an overline on an operator denotes graph closure.
--
--   Let $K$ be a Hilbert space and let $U:H\to K$ be a linear isometric isomorphism. Then
--
--   $$\Psi(f):=U\Phi(f)U^{-1}\qquad(f\in M(X))$$
--
--   is a measurable calculus on $K$. The graph and domain are transported by $U$.
--
--   This is change of Hilbert space by a given unitary.
-- source:
--   The Functional Calculus Approach to the Spectral Theorem, arXiv:2003.06130v2, PDF p. 11, §2.6, unnumbered: unitary transport

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

/-- Section 2.6, PDF p.11: unitary unitaryGraphTransport of the whole calculus. -/
theorem calculus_unitary_transport (F : Symbol X k → Relation H) (hF : Calculus F)
    (U : H ≃ₗᵢ[k] K) : Calculus (fun f => unitaryGraphTransport U (F f)) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P05

end
