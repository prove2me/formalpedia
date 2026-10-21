-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P05_calculus_domination_polynomial
-- name    : QAlgorithms.Papers.Independent.Claimed50.P05.calculus_domination_polynomial
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T09:00:59.8011+00:00
-- url     : https://prove2.me/theorems/fcfc5dd6-72ba-4ab2-8932-91bf6fcee924
-- title:
--   Corollary 2.3
-- statement:
--   Let $k$ be $\mathbb R$ or $\mathbb C$, let $H$ be a Hilbert space, and let $(X,\Sigma)$ be a measurable space. Write $M(X)$ for the finite $k$-valued measurable functions with pointwise equality, and $M_b(X)$ for its bounded functions. Let $\Phi:M(X)\to C(H)$ satisfy axioms MFC1–MFC5, where $C(H)$ consists of closed functional linear graphs. All operator equalities include equality of domains; an overline on an operator denotes graph closure.
--
--   For $f,g\in M(X)$, pointwise domination $|f|\le|g|$ implies
--
--   $$\operatorname{dom}\Phi(g)\subseteq\operatorname{dom}\Phi(f),\qquad\|\Phi(f)x\|\le\|\Phi(g)x\|\quad(x\in\operatorname{dom}\Phi(g)).$$
--
--   For every $f$, the operators $\Phi(f)$ and $\Phi(|f|)$ have the same domain and equal output norms on it. For every nonzero polynomial $p(z)=\sum_{j=0}^{n}a_jz^j\in k[z]$ of exact degree $n\ge0$,
--
--   $$\Phi(p(f))=p(\Phi(f))=\sum_{j=0}^n a_j\Phi(f)^j,\qquad\operatorname{dom}\Phi(p(f))=\operatorname{dom}(\Phi(f)^n).$$
--
--   The finite sum uses the actual partial-operator products and all coefficient terms, including zero coefficients.
--
--   This identifies domains through magnitude and polynomial growth.
-- source:
--   The Functional Calculus Approach to the Spectral Theorem, arXiv:2003.06130v2, PDF p. 6, Corollary 2.3

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

/-- Corollary 2.3, PDF pp.6–7: domination, absolute value, and exact polynomial domains. -/
theorem calculus_domination_polynomial (F : Symbol X k → Relation H) (hF : Calculus F) :
    (∀ f g, (∀ x, ‖f.val x‖ ≤ ‖g.val x‖) →
      graphDomain (F g) ⊆ graphDomain (F f) ∧
      ∀ x y z, (x, y) ∈ F f → (x, z) ∈ F g → ‖y‖ ≤ ‖z‖) ∧
    (∀ f, graphDomain (F f) = graphDomain (F (absolute f)) ∧
      ∀ x y z, (x, y) ∈ F f → (x, z) ∈ F (absolute f) → ‖y‖ = ‖z‖) ∧
    (∀ (f : Symbol X k) (p : Polynomial k) (n : ℕ), p ≠ 0 → p.natDegree = n →
      F (polynomialSymbol p f) = polynomialGraph p (F f) ∧
      graphDomain (F (polynomialSymbol p f)) = graphDomain (graphPower (F f) n)) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P05

end
