-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P02_measureSupport_exists
-- name    : QAlgorithms.Papers.Independent.Renew46.P02.measureSupport_exists
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T19:45:43.360227+00:00
-- url     : https://prove2.me/theorems/947e582d-76a0-42b2-8c53-b0bd6458ed34
-- title:
--   Lemma 4.1: Existence of measure support
-- statement:
--   Let $\mu$ be a positive measure on a measurable space $(X,\Sigma)$. A $\mu$-support for $\nu$ is a measurable set $S$ with $\nu(S^c)=0$ such that $\nu(E)>0$ whenever $E\in\Sigma$, $E\subseteq S$, and $\mu(E)>0$. Then both assertions hold:
--
--   $$
--   \mu(X)<\infty\ \Longrightarrow\ \forall\nu\ll\mu,\ \nu\text{ has }\mu\text{-support},
--   \qquad
--   f:X\to[0,\infty]\text{ measurable}\ \Longrightarrow\ \mu_f\text{ has }\mu\text{-support},
--   $$
--
--   where $\mu_f(E)=\int_E f\,d\mu$. In the second assertion the density may be infinite. This supplies supports for subsequent Radon–Nikodym statements.
-- source:
--   Abelian von Neumann algebras, measure algebras and L^\infty-spaces, arXiv:2108.06406v2, PDF p. 12, Lemma 4.1

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P02

noncomputable section

open MeasureTheory Set

open scoped ENNReal Topology CompactlySupported

namespace QAlgorithms.Papers.Independent.Renew46.P02

universe u v

/-- Lemma 4.1, PDF p.12: both finite-base support and support of any
measurable extended nonnegative density are retained. -/
theorem measureSupport_exists {X : Type u} [MeasurableSpace X] (mu : Measure X) :
    ((mu Set.univ < ⊤) → ∀ nu : Measure X, nu ≪ mu → HasMeasureSupport mu nu) ∧
    (∀ f : X → ℝ≥0∞, Measurable f → HasMeasureSupport mu (mu.withDensity f)) := by sorry

end QAlgorithms.Papers.Independent.Renew46.P02

end
