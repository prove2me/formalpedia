-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P05_calculus_projection_measure
-- name    : QAlgorithms.Papers.Independent.Claimed50.P05.calculus_projection_measure
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T09:05:35.193986+00:00
-- url     : https://prove2.me/theorems/002ea64d-e4e6-4ed8-a027-184eb61d8059
-- title:
--   §3, unnumbered: associated projection-valued measure
-- statement:
--   Let $k$ be $\mathbb R$ or $\mathbb C$, let $H$ be a Hilbert space, and let $(X,\Sigma)$ be a measurable space. Write $M(X)$ for the finite $k$-valued measurable functions with pointwise equality, and $M_b(X)$ for its bounded functions. Let $\Phi:M(X)\to C(H)$ satisfy axioms MFC1–MFC5, where $C(H)$ consists of closed functional linear graphs. All operator equalities include equality of domains; an overline on an operator denotes graph closure.
--
--   The indicator operators
--
--   $$E_\Phi(A):=\Phi(1_A)\qquad(A\in\Sigma)$$
--
--   form a projection-valued measure: every $E_\Phi(A)$ is an everywhere-defined orthogonal projection, $E_\Phi(X)=I$, and $E_\Phi(\bigcup_n A_n)x=\sum_n E_\Phi(A_n)x$ for all $x\in H$ whenever the measurable $A_n$ are pairwise disjoint. The series converges in the norm of $H$.
--
--   This extracts spectral projections from a calculus.
-- source:
--   The Functional Calculus Approach to the Spectral Theorem, arXiv:2003.06130v2, PDF p. 13, §3, unnumbered: associated projection-valued measure

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

/-- Section 3, PDF p.13: associated projection-valued measure, including strong disjoint additivity. -/
theorem calculus_projection_measure (F : Symbol X k → Relation H) (hF : Calculus F) :
    PVM (k := k) (fun A => F (indicator A.val A.property)) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P05

end
