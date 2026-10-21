-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P02_riesz_fullSupportCompact
-- name    : QAlgorithms.Papers.Independent.Renew46.P02.riesz_fullSupportCompact
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T19:48:50.013659+00:00
-- url     : https://prove2.me/theorems/9afb269a-51eb-4ea1-a919-9307a46fd97f
-- title:
--   Lemma 6.3: Full-support compact subset
-- statement:
--   Let $X$ be locally compact Hausdorff and $I:C_c(X,\mathbb C)\to\mathbb C$ positive and complex linear. Let $\mu_0$ be the inner-regular Borel part of the Riesz construction on pp.22–23: take the open-set supremum from $I$, its open-envelope infimum $m^*$, and then $\mu_0(E)=\sup_{C\subseteq E,\ C\text{ compact}}m^*(C)$. If $K\subseteq X$ is compact and $\mu_0(K)>0$, there exists a compact $K_0\subseteq K$ such that
--
--   $$
--   \mu_0(K_0)=\mu_0(K),\qquad
--   U\text{ open},\ U\cap K_0\ne\varnothing\ \Longrightarrow\ \mu_0(U\cap K_0)>0.
--   $$
--
--   The compact subset retains all mass and has full relative support. The measure in every clause is the one constructed from the same functional.
-- source:
--   Abelian von Neumann algebras, measure algebras and L^\infty-spaces, arXiv:2108.06406v2, PDF p. 25, Lemma 6.3

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P02

noncomputable section

open MeasureTheory Set

open scoped ENNReal Topology CompactlySupported

namespace QAlgorithms.Papers.Independent.Renew46.P02

universe u v

/-- Lemma 6.3, PDF p.25. The same constructed mu_0 is used throughout. -/
theorem riesz_fullSupportCompact {X : Type u} [TopologicalSpace X]
    [T2Space X] [LocallyCompactSpace X] (I : C_c(X, ℂ) →ₗ[ℂ] ℂ)
    (hI : IsPositiveRieszFunctional I) (K : Set X)
    (hK : IsCompact K) (hpos : 0 < rieszBorelPart I K) :
    ∃ K0 : Set X, K0 ⊆ K ∧ IsCompact K0 ∧ rieszBorelPart I K0 = rieszBorelPart I K ∧
      ∀ U : Set X, IsOpen U → (U ∩ K0).Nonempty →
        0 < rieszBorelPart I (U ∩ K0) := by sorry

end QAlgorithms.Papers.Independent.Renew46.P02

end
