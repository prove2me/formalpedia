-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P05_calculus_closed_subspace
-- name    : QAlgorithms.Papers.Independent.Claimed50.P05.calculus_closed_subspace
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T09:03:00.272238+00:00
-- url     : https://prove2.me/theorems/08afb4bd-fafc-40e5-bc3b-70415504f065
-- title:
--   Lemma 2.6
-- statement:
--   Let $k$ be $\mathbb R$ or $\mathbb C$, let $H$ be a Hilbert space, and let $(X,\Sigma)$ be a measurable space. Write $M(X)$ for the finite $k$-valued measurable functions with pointwise equality, and $M_b(X)$ for its bounded functions. Let $\Phi:M(X)\to C(H)$ satisfy axioms MFC1–MFC5, where $C(H)$ consists of closed functional linear graphs. All operator equalities include equality of domains; an overline on an operator denotes graph closure.
--
--   Let $S\subseteq H$ be a closed linear subspace, and let $P$ be its orthogonal projection. Define $\Phi_S(f)$ by the part graph $\Phi(f)\cap(S\times S)$. It satisfies MFC1–MFC3 independently of invariance. Furthermore,
--
--   $$\begin{aligned}
--   \Phi_S\text{ is a measurable calculus}
--   &\Longleftrightarrow (\forall f\in M_b(X))\ \Phi_S(f)\in L(S)\\
--   &\Longleftrightarrow S\text{ is invariant under every }\Phi(f),\ f\in M_b(X)\\
--   &\Longleftrightarrow (\forall f\in M_b(X))\ \Phi(f)P=P\Phi(f).
--   \end{aligned}$$
--
--   This characterizes restriction to a closed Hilbert subspace.
-- source:
--   The Functional Calculus Approach to the Spectral Theorem, arXiv:2003.06130v2, PDF p. 11, Lemma 2.6

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

/-- Lemma 2.6, PDF p.11: parts in a closed subspace and the four equivalent invariance criteria. -/
theorem calculus_closed_subspace (F : Symbol X k → Relation H) (hF : Calculus F)
    (S : Submodule k H) (hS : IsClosed (S : Set H)) (P : H →L[k] H)
    (hP : ProjectionOnto (k := k) (boundedGraph P) (S : Set H)) :
    ProtoCalculus (part F S) ∧
    ((Calculus (part F S) ↔ ∀ f, BoundedSymbol f → BoundedOperator (k := k) (part F S f)) ∧
     (Calculus (part F S) ↔ ∀ f, BoundedSymbol f →
       ∀ x y, x ∈ S → (x, y) ∈ F f → y ∈ S) ∧
     (Calculus (part F S) ↔ ∀ f, BoundedSymbol f → mul (F f) (boundedGraph P) = mul (boundedGraph P) (F f))) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P05

end
