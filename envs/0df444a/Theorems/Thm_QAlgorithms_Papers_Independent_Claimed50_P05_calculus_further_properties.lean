-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P05_calculus_further_properties
-- name    : QAlgorithms.Papers.Independent.Claimed50.P05.calculus_further_properties
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T09:01:42.154654+00:00
-- url     : https://prove2.me/theorems/d3b17455-4a2d-4682-a7e5-7f1d5b5279c8
-- title:
--   Theorem 2.4
-- statement:
--   Let $k$ be $\mathbb R$ or $\mathbb C$, let $H$ be a Hilbert space, and let $(X,\Sigma)$ be a measurable space. Write $M(X)$ for the finite $k$-valued measurable functions with pointwise equality, and $M_b(X)$ for its bounded functions. Let $\Phi:M(X)\to C(H)$ satisfy axioms MFC1–MFC5, where $C(H)$ consists of closed functional linear graphs. All operator equalities include equality of domains; an overline on an operator denotes graph closure.
--
--   For every $f,g\in M(X)$, $\operatorname{dom}\Phi(f)\cap\operatorname{dom}\Phi(g)$ is a core for $\Phi(g)$, meaning graph density of the restriction. Moreover,
--
--   $$\overline{\Phi(f)+\Phi(g)}=\Phi(f+g),\quad\overline{\Phi(f)\Phi(g)}=\Phi(fg),\quad\Phi(f)^*=\Phi(\overline f).$$
--
--   Each $\Phi(f)$ is normal and $\Phi(\overline f)\Phi(f)=\Phi(|f|^2)$. Real-valued $f$ gives a self-adjoint operator. If real-valued $f\le g$, then $\langle x,\Phi(f)x\rangle\le\langle x,\Phi(g)x\rangle$ on the intersection of their domains. The set $\operatorname{bdd}(\Phi)=\{f:\Phi(f)\in L(H)\}$ is a unital star subalgebra, and its restriction under $\Phi$ is a unital star homomorphism. Finally, if $f_n\to f$ pointwise and there is one real $C$ with $\|\Phi(f_n)\|\le C$ for every $n$, then $\Phi(f)$ is bounded and $\Phi(f_n)\to\Phi(f)$ strongly on all of $H$. Pairings use the convention linear in the second entry.
--
--   These properties supply closed graph identities and uniform operator convergence.
-- source:
--   The Functional Calculus Approach to the Spectral Theorem, arXiv:2003.06130v2, PDF p. 8, Theorem 2.4

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

/-- Theorem 2.4, PDF pp.8–10: boundedGraph closures, adjoints, normality, order, and strong convergence. -/
theorem calculus_further_properties (F : Symbol X k → Relation H) (hF : Calculus F) :
    (∀ f g, GraphCore (F g) (graphDomain (F f) ∩ graphDomain (F g))) ∧
    (∀ f g, closure (add (F f) (F g)) = F (plus f g) ∧
      closure (mul (F f) (F g)) = F (times f g)) ∧
    (∀ f, graphAdjoint (k := k) (F f) = F (starSymbol f)) ∧
    (∀ f, Normal (k := k) (F f) ∧
      mul (F (starSymbol f)) (F f) = F (times (absolute f) (absolute f))) ∧
    ((∀ f, RealValued f → SelfAdjoint (k := k) (F f)) ∧
      ∀ f g, RealValued f → RealValued g → RealLE f g →
        ∀ x y z, (x, y) ∈ F f → (x, z) ∈ F g →
          RCLike.re (inner k x y) ≤ RCLike.re (inner k x z)) ∧
    (BoundedRestrictionHom F ∧
      ∀ fn f, Pointwise fn f → (∃ c : ℝ, ∀ n, NormBound (k := k) (F (fn n)) c) →
        BoundedOperator (k := k) (F f) ∧ Strong (k := k) (fun n => F (fn n)) (F f)) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P05

end
