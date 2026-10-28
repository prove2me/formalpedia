-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P02_semifinitePart_exists
-- name    : QAlgorithms.Papers.Independent.Renew46.P02.semifinitePart_exists
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T19:46:16.77584+00:00
-- url     : https://prove2.me/theorems/8ca480db-ebe1-4c50-bb9f-7cb76cb16702
-- title:
--   Lemma 4.2: Semifinite and anti-semifinite parts
-- statement:
--   Let $(X,\Sigma,\mu)$ be Dedekind: every family of measurable sets has an essential supremum for inclusion modulo $\mu$-null sets. Let $\mathcal F=\{E\in\Sigma:0<\mu(E)<\infty\}$. There is a measurable essential supremum $S$ of $\mathcal F$ such that
--
--   $$
--   \mu|_S\text{ is semifinite and Dedekind},\qquad
--   E\in\Sigma,\ E\subseteq S^c,\ \mu(E)>0\ \Longrightarrow\ \mu(E)=\infty.
--   $$
--
--   Moreover, for every $\nu\ll\mu$ that is $\mu$-semifinite, $\nu$ has $\mu$-support, its restriction to $S$ is $\mu|_S$-semifinite, and $\nu(E)=0$ for every measurable $E\subseteq S^c$. Here relative semifiniteness means that every measurable set of positive $\nu$-measure has a measurable subset of finite $\mu$-measure and positive $\nu$-measure; finite $\nu$-measure is not required. This separates the canonical semifinite and anti-semifinite parts.
-- source:
--   Abelian von Neumann algebras, measure algebras and L^\infty-spaces, arXiv:2108.06406v2, PDF p. 12, Lemma 4.2

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P02

noncomputable section

open MeasureTheory Set

open scoped ENNReal Topology CompactlySupported

namespace QAlgorithms.Papers.Independent.Renew46.P02

universe u v

/-- Lemma 4.2, PDF pp.12--13: the constructed semifinite part is Dedekind,
its complement is anti-semifinite, and relative semifiniteness gives support
and vanishing on every measurable subset of the complement. -/
theorem semifinitePart_exists {X : Type u} [MeasurableSpace X]
    (mu : Measure X) (hded : IsDedekindOn mu Set.univ) :
    ∃ S : Set X, IsSemifinitePart mu S ∧ IsSemifiniteOn mu S ∧ IsDedekindOn mu S ∧
      (∀ E : Set X, MeasurableSet E → E ⊆ Sᶜ → 0 < mu E → mu E = ⊤) ∧
      (∀ nu : Measure X, nu ≪ mu → IsRelativeSemifiniteOn mu nu Set.univ →
        HasMeasureSupport mu nu ∧ IsRelativeSemifiniteOn mu nu S ∧
          ∀ E : Set X, MeasurableSet E → E ⊆ Sᶜ → nu E = 0) := by sorry

end QAlgorithms.Papers.Independent.Renew46.P02

end
