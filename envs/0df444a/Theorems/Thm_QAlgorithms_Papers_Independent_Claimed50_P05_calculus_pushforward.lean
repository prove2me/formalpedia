-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P05_calculus_pushforward
-- name    : QAlgorithms.Papers.Independent.Claimed50.P05.calculus_pushforward
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T09:04:15.349757+00:00
-- url     : https://prove2.me/theorems/53baec3a-330e-47e1-8330-37bc26800369
-- title:
--   Corollary 2.8
-- statement:
--   Let $k$ be $\mathbb R$ or $\mathbb C$, let $H$ be a Hilbert space, and let $(X,\Sigma)$ be a measurable space. Write $M(X)$ for the finite $k$-valued measurable functions with pointwise equality, and $M_b(X)$ for its bounded functions. Let $\Phi:M(X)\to C(H)$ satisfy axioms MFC1–MFC5, where $C(H)$ consists of closed functional linear graphs. All operator equalities include equality of domains; an overline on an operator denotes graph closure.
--
--   For a measurable map $\varphi:X\to Y$ into another measurable space, the map
--
--   $$\Phi^\varphi(g):=\Phi(g\circ\varphi)\qquad(g\in M(Y))$$
--
--   is a measurable functional calculus on $Y$.
--
--   This is push-forward in the base space.
-- source:
--   The Functional Calculus Approach to the Spectral Theorem, arXiv:2003.06130v2, PDF p. 12, Corollary 2.8

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

/-- Corollary 2.8, PDF p.12: push-forward along a measurable map. -/
theorem calculus_pushforward (F : Symbol X k → Relation H) (hF : Calculus F)
    (p : X → Y) (hp : Measurable p) : Calculus (push F p hp) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P05

end
