-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P05_calculus_support_concentration
-- name    : QAlgorithms.Papers.Independent.Claimed50.P05.calculus_support_concentration
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T09:06:42.291625+00:00
-- url     : https://prove2.me/theorems/fe02e472-e5b6-4ffe-99e0-1c1e6783a92b
-- title:
--   Proposition 3.2
-- statement:
--   Let $k$ be $\mathbb R$ or $\mathbb C$, let $H$ be a Hilbert space, and let $(X,\Sigma)$ be a measurable space. Write $M(X)$ for the finite $k$-valued measurable functions with pointwise equality, and $M_b(X)$ for its bounded functions. Let $\Phi:M(X)\to C(H)$ satisfy axioms MFC1–MFC5, where $C(H)$ consists of closed functional linear graphs. All operator equalities include equality of domains; an overline on an operator denotes graph closure.
--
--   Suppose $X$ is second countable and $\Sigma$ is its Borel sigma algebra. Define $\operatorname{supp}\Phi$ to be the complement of the union of all open $\Phi$-null sets. Then
--
--   $$X\setminus\operatorname{supp}\Phi\text{ is }\Phi\text{-null}.$$
--
--   Thus $\Phi$ is concentrated on its support.
--
--   This identifies a closed concentration set using second countability.
-- source:
--   The Functional Calculus Approach to the Spectral Theorem, arXiv:2003.06130v2, PDF p. 15, Proposition 3.2

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

/-- Proposition 3.2, PDF p.15: calculusSupport concentration requires second countability. -/
theorem calculus_support_concentration [TopologicalSpace X] [BorelSpace X]
    [SecondCountableTopology X] (F : Symbol X k → Relation H) (hF : Calculus F) :
    Concentrated F (calculusSupport F) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P05

end
