-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P05_calculus_regularization
-- name    : QAlgorithms.Papers.Independent.Claimed50.P05.calculus_regularization
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T09:21:12.578977+00:00
-- url     : https://prove2.me/theorems/b62fd65d-bc2e-418d-9812-82afe1013158
-- title:
--   §2.4, unnumbered: canonical determination by bounded functions
-- statement:
--   Let $k$ be $\mathbb R$ or $\mathbb C$, let $H$ be a Hilbert space, and let $(X,\Sigma)$ be a measurable space. Write $M(X)$ for the finite $k$-valued measurable functions with pointwise equality, and $M_b(X)$ for its bounded functions. Let $\Phi:M(X)\to C(H)$ satisfy axioms MFC1–MFC5, where $C(H)$ consists of closed functional linear graphs. All operator equalities include equality of domains; an overline on an operator denotes graph closure.
--
--   For arbitrary $f\in M(X)$ put $e=(1+|f|)^{-1}$. Then $e,ef$ are bounded, their calculus images are bounded, $\Phi(e)$ is injective, and
--
--   $$\Phi(f)=\Phi(e)^{-1}\Phi(ef),\qquad (x,y)\in\Phi(f)\ \Longleftrightarrow\ \Phi(ef)x=\Phi(e)y.$$
--
--   The final equivalence holds for all $x,y\in H$; it does not apply an unbounded operator outside its domain.
--
--   This computes every unbounded graph from two bounded images.
-- source:
--   The Functional Calculus Approach to the Spectral Theorem, arXiv:2003.06130v2, PDF p. 10, §2.4, unnumbered: canonical determination by bounded functions

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

/-- Section 2.4, PDF p.10: canonical regularization, including its exact boundedGraph equivalence. -/
theorem calculus_regularization (F : Symbol X k → Relation H) (hF : Calculus F) (f : Symbol X k) :
    BoundedSymbol (regularizer f) ∧ BoundedSymbol (times (regularizer f) f) ∧
    BoundedOperator (k := k) (F (regularizer f)) ∧
    BoundedOperator (k := k) (F (times (regularizer f) f)) ∧
    InjectiveOperator (F (regularizer f)) ∧
    F f = mul (inverse (F (regularizer f))) (F (times (regularizer f) f)) ∧
    ∀ x y, (x, y) ∈ F f ↔
      ∃ z, (x, z) ∈ F (times (regularizer f) f) ∧ (y, z) ∈ F (regularizer f) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P05

end
