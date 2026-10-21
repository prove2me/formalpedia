-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P02_riesz_localMeasurability
-- name    : QAlgorithms.Papers.Independent.Renew46.P02.riesz_localMeasurability
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T19:47:29.452501+00:00
-- url     : https://prove2.me/theorems/9eec95f5-ef81-457c-839d-d210a53be67d
-- title:
--   Proposition 6.1: Local test for Caratheodory measurability
-- statement:
--   Let $X$ be locally compact Hausdorff and let $I:C_c(X,\mathbb C)\to\mathbb C$ be a positive complex linear functional. Use the construction on pp.22–23: $m(U)$ is the supremum of $I(f)$ for $0\le f\le1$ with compact support contained in the open set $U$; $m^*(A)=\inf_{U\supseteq A}m(U)$ over open $U$; $\mu_0(E)=\sup_{K\subseteq E}m^*(K)$ over compact $K$; and $\mu_0^*(A)=\inf_{B\supseteq A}\mu_0(B)$ over Borel $B$. Write $\mathcal M$ for the full Caratheodory measurable domain of $\mu_0^*$. For every subset $E\subseteq X$,
--
--   $$
--   E\in\mathcal M
--   \iff \bigl[ E\cap U\in\mathcal M\text{ for every open }U\text{ with }\mu_0(U)<\infty\bigr]
--   \iff \bigl[E\cap K\in\mathcal M\text{ for every compact }K\bigr].
--   $$
--
--   This gives local measurability tests for the specified extension, rather than for an arbitrary Borel measure.
-- source:
--   Abelian von Neumann algebras, measure algebras and L^\infty-spaces, arXiv:2108.06406v2, PDF p. 23, Proposition 6.1

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P02

noncomputable section

open MeasureTheory Set

open scoped ENNReal Topology CompactlySupported

namespace QAlgorithms.Papers.Independent.Renew46.P02

universe u v

/-- Proposition 6.1, PDF pp.23--24. Every test uses the same explicitly
constructed outer extension of the given positive functional. -/
theorem riesz_localMeasurability {X : Type u} [TopologicalSpace X]
    [T2Space X] [LocallyCompactSpace X] (I : C_c(X, ℂ) →ₗ[ℂ] ℂ)
    (hI : IsPositiveRieszFunctional I) (E : Set X) :
    (IsCaratheodorySet (rieszExtension I) E ↔
      ∀ U : Set X, IsOpen U → rieszBorelPart I U < ⊤ →
        IsCaratheodorySet (rieszExtension I) (E ∩ U)) ∧
    (IsCaratheodorySet (rieszExtension I) E ↔
      ∀ K : Set X, IsCompact K → IsCaratheodorySet (rieszExtension I) (E ∩ K)) := by sorry

end QAlgorithms.Papers.Independent.Renew46.P02

end
