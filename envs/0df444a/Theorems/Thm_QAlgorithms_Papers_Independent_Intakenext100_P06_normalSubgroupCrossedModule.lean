-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P06_normalSubgroupCrossedModule
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P06.normalSubgroupCrossedModule
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T22:51:47.887993+00:00
-- url     : https://prove2.me/theorems/5ce57c8c-d4b8-42e0-a556-662f7b4f95b3
-- title:
--   A normal subgroup gives a crossed module
-- statement:
--   Let $G$ be an arbitrary group and $H\trianglelefteq G$ any normal subgroup. Let $t:H\to G$ be inclusion and let $\rho(g)(h)=ghg^{-1}$. Then
--
--   $$
--   t(\rho(g)h)=g\,t(h)\,g^{-1},\qquad
--   \rho(t(h))(k)=hkh^{-1}.
--   $$
--
--   Thus $(G,H,t,\rho)$ is a crossed module. The trivial subgroup and the whole group are allowed; no universal nonskeletality assertion is made.
-- source:
--   Hoàng Xuân Sính's Thesis: Categorifying Group Theory, arXiv:2308.05119v2, PDF p. 10, §4: normal subgroup example

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P06

namespace QAlgorithms.Papers.Independent.Intakenext100.P06

open CategoryTheory CategoryTheory.MonoidalCategory

open QAlgorithms.Papers.Independent.Gap48.P14

open QAlgorithms.Papers.Independent.Renew46.P18

universe u v u1 v1 w

attribute [local instance] QAlgorithms.Papers.Independent.Intakenext100.P06.singletonSymmetric

/-- Section 4, Definition 3 and normal-subgroup example, PDF p. 10.
The subgroup may be trivial or the entire group. -/
theorem normalSubgroupCrossedModule {G : Type u} [Group G]
    (H : Subgroup G) [H.Normal] :
    IsCrossedModule H.subtype (MulAut.conjNormal : G →* MulAut H) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P06
