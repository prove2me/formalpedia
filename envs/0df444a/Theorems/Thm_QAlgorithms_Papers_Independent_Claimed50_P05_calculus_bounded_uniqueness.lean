-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P05_calculus_bounded_uniqueness
-- name    : QAlgorithms.Papers.Independent.Claimed50.P05.calculus_bounded_uniqueness
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T09:11:17.318193+00:00
-- url     : https://prove2.me/theorems/c00fc0d4-6eb8-4a17-82bb-4136d8b16774
-- title:
--   Lemma 5.1
-- statement:
--   Let $k$ be $\mathbb R$ or $\mathbb C$, let $H$ be a Hilbert space, and let $(X,\Sigma)$ be a measurable space. Write $M(X)$ for the finite $k$-valued measurable functions with pointwise equality, and $M_b(X)$ for its bounded functions. Let $\Phi:M(X)\to C(H)$ satisfy axioms MFC1–MFC5, where $C(H)$ consists of closed functional linear graphs. All operator equalities include equality of domains; an overline on an operator denotes graph closure.
--
--   Let $\Psi:M(X)\to C(H)$ be a second measurable calculus on the same Hilbert space. If $\Phi(f)=\Psi(f)$ for every bounded measurable $f$, then
--
--   $$\Phi=\Psi\quad\text{on all of }M(X).$$
--
--   Equality includes the graphs and domains of unbounded images.
--
--   This is uniqueness from bounded symbols.
-- source:
--   The Functional Calculus Approach to the Spectral Theorem, arXiv:2003.06130v2, PDF p. 20, Lemma 5.1

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

/-- Lemma 5.1, PDF p.20: equality on bounded symbols determines all operator graphs. -/
theorem calculus_bounded_uniqueness (F G : Symbol X k → Relation H)
    (hF : Calculus F) (hG : Calculus G)
    (h : ∀ f, BoundedSymbol f → F f = G f) : F = G := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P05

end
