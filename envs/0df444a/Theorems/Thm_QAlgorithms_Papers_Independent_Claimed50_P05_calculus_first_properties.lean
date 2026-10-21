-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P05_calculus_first_properties
-- name    : QAlgorithms.Papers.Independent.Claimed50.P05.calculus_first_properties
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T08:59:59.04498+00:00
-- url     : https://prove2.me/theorems/d238b174-5444-4e7c-879a-30cbf0cb895d
-- title:
--   Theorem 2.1
-- statement:
--   Let $k$ be $\mathbb R$ or $\mathbb C$, let $H$ be a Hilbert space, and let $(X,\Sigma)$ be a measurable space. Write $M(X)$ for the finite $k$-valued measurable functions with pointwise equality, and $M_b(X)$ for its bounded functions. Let $\Phi:M(X)\to C(H)$ satisfy axioms MFC1–MFC5, where $C(H)$ consists of closed functional linear graphs. All operator equalities include equality of domains; an overline on an operator denotes graph closure.
--
--   For $f,g\in M(X)$, $\lambda\in k$, and a sequence $(f_n)$ in $M(X)$, the following six conclusions hold.
--
--   $$
--   \begin{aligned}
--   &\lambda\ne0\ \text{or}\ \Phi(f)\in L(H)\quad\Longrightarrow\quad\Phi(\lambda f)=\lambda\Phi(f),\\
--   &\Phi(g)\in L(H)\quad\Longrightarrow\quad\Phi(f)+\Phi(g)=\Phi(f+g),\quad\Phi(f)\Phi(g)=\Phi(fg),\quad\Phi(g)\Phi(f)\subseteq\Phi(f)\Phi(g),\\
--   &f\ne0\ \text{everywhere}\quad\Longrightarrow\quad\Phi(f)\text{ is injective and }\Phi(f)^{-1}=\Phi(f^{-1}),\\
--   &\overline{\operatorname{dom}\Phi(f)}=H,\\
--   &f\in M_b(X)\quad\Longrightarrow\quad\|\Phi(f)\|\le\|f\|_\infty,\\
--   &f_n\to f\text{ pointwise},\quad\sup_n\|f_n\|_\infty<\infty\quad\Longrightarrow\quad\Phi(f_n)\to\Phi(f)\text{ strongly}.
--   \end{aligned}
--   $$
--
--   Here $L(H)$ denotes everywhere-defined bounded linear operators, and an injective operator's inverse acts on its range.
--
--   These are the first algebraic, domain, and continuity consequences of the calculus axioms.
-- source:
--   The Functional Calculus Approach to the Spectral Theorem, arXiv:2003.06130v2, PDF p. 5, Theorem 2.1

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

/-- Theorem 2.1, PDF pp.5–6: all six clauses, with scalars in the ambient field.
Source correction (independently audited in moderation round 1).
Printed: Theorem 2.1 quantifies lambda in C in the section generic over K in {R,C}.
Changed: Quantify the scalar c in the ambient field k, as in axiom MFC2; retain all six conclusions.
Why: Complex scalar multiplication is not defined on an arbitrary real Hilbert space. The standing field convention and MFC2 determine the intended scalar type.
-/
theorem calculus_first_properties (F : Symbol X k → Relation H) (hF : Calculus F) :
    (∀ c f, c ≠ 0 ∨ BoundedOperator (k := k) (F f) → F (scalar c f) = scale c (F f)) ∧
    (∀ f g, BoundedOperator (k := k) (F g) →
      add (F f) (F g) = F (plus f g) ∧ mul (F f) (F g) = F (times f g) ∧
      mul (F g) (F f) ⊆ mul (F f) (F g)) ∧
    (∀ f, (∀ x, f.val x ≠ 0) → InjectiveOperator (F f) ∧ inverse (F f) = F (reciprocal f)) ∧
    (∀ f, Dense (graphDomain (F f))) ∧
    (∀ f, BoundedSymbol f → NormBound (k := k) (F f) (symbolNorm f)) ∧
    (∀ fn f, BP fn f → Strong (k := k) (fun n => F (fn n)) (F f)) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P05

end
