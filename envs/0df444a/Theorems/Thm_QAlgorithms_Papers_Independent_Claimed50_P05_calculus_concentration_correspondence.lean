-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P05_calculus_concentration_correspondence
-- name    : QAlgorithms.Papers.Independent.Claimed50.P05.calculus_concentration_correspondence
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T09:22:24.576371+00:00
-- url     : https://prove2.me/theorems/8c7dd396-201e-400a-ad77-a32e3ef70024
-- title:
--   §3.2, unnumbered: restriction and extension correspondence
-- statement:
--   Let $k$ be $\mathbb R$ or $\mathbb C$, let $H$ be a Hilbert space, and let $(X,\Sigma)$ be a measurable space. Write $M(X)$ for the finite $k$-valued measurable functions with pointwise equality, and $M_b(X)$ for its bounded functions. Let $\Phi:M(X)\to C(H)$ satisfy axioms MFC1–MFC5, where $C(H)$ consists of closed functional linear graphs. All operator equalities include equality of domains; an overline on an operator denotes graph closure.
--
--   Fix a measurable $S\subseteq X$. If a calculus $\Phi$ on $X$ is concentrated on $S$, set $\Phi_S(f)=\Phi(f^S)$, where $f^S$ is $f$ on $S$ and zero elsewhere. Conversely, for a calculus $\Psi$ on $S$ with the trace sigma algebra, set $\Psi^X(g)=\Psi(g|_S)$. Both constructions yield measurable calculi, the latter is concentrated on $S$, and
--
--   $$(\Phi_S)^X=\Phi,\qquad(\Psi^X)_S=\Psi.$$
--
--   Thus they are inverse correspondences. This is a restriction of the base, distinct from taking a part in a Hilbert subspace.
--
--   This identifies concentrated calculi with calculi on the smaller measurable base.
-- source:
--   The Functional Calculus Approach to the Spectral Theorem, arXiv:2003.06130v2, PDF p. 14, §3.2, unnumbered: restriction and extension correspondence

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

/-- Section 3.2, PDF pp.14–15: the two specified constructions are mutually inverse. -/
theorem calculus_concentration_correspondence (S : Set X) (hS : MeasurableSet S) :
    (∀ F : Symbol X k → Relation H, Calculus F → Concentrated F S →
      Calculus (restrictBase F S hS) ∧ extendBase (restrictBase F S hS) = F) ∧
    (∀ G : Symbol S k → Relation H, Calculus G →
      Calculus (extendBase G) ∧ Concentrated (extendBase G) S ∧
        restrictBase (extendBase G) S hS = G) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P05

end
