-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P05_calculus_pvm_uniqueness
-- name    : QAlgorithms.Papers.Independent.Claimed50.P05.calculus_pvm_uniqueness
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T09:11:58.55572+00:00
-- url     : https://prove2.me/theorems/3d15081e-ceaf-456d-b401-98e2e7a26ad4
-- title:
--   Proposition 5.2
-- statement:
--   Let $k$ be $\mathbb R$ or $\mathbb C$, let $H$ be a Hilbert space, and let $(X,\Sigma)$ be a measurable space. Write $M(X)$ for the finite $k$-valued measurable functions with pointwise equality, and $M_b(X)$ for its bounded functions. Let $\Phi:M(X)\to C(H)$ satisfy axioms MFC1–MFC5, where $C(H)$ consists of closed functional linear graphs. All operator equalities include equality of domains; an overline on an operator denotes graph closure.
--
--   Let $\Psi$ be another measurable calculus on the same base and Hilbert space. If $\Phi(1_A)=\Psi(1_A)$ for every $A\in\Sigma$, then
--
--   $$\Phi=\Psi.$$
--
--   Thus equality of the associated projection-valued measures determines the full calculi.
--
--   This is uniqueness from spectral projections.
-- source:
--   The Functional Calculus Approach to the Spectral Theorem, arXiv:2003.06130v2, PDF p. 20, Proposition 5.2

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

/-- Proposition 5.2, PDF p.20: equality of all measurable spectral projections implies equality. -/
theorem calculus_pvm_uniqueness (F G : Symbol X k → Relation H)
    (hF : Calculus F) (hG : Calculus G)
    (h : ∀ A (hA : MeasurableSet A), F (indicator A hA) = G (indicator A hA)) : F = G := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P05

end
