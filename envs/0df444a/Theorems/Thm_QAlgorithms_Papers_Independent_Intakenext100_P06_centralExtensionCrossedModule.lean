-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P06_centralExtensionCrossedModule
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P06.centralExtensionCrossedModule
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T22:52:10.663021+00:00
-- url     : https://prove2.me/theorems/4b8414a4-08ac-4673-89a1-b0ac6f9f9b7e
-- title:
--   A central extension gives a section-independent crossed module
-- statement:
--   Let $1\to C\xrightarrow{i}H\xrightarrow{t}G\to1$ be a short exact sequence of arbitrary groups, with $i(C)$ central in $H$. There is an automorphic action $\rho:G\to\operatorname{Aut}(H)$ such that for every set-theoretic section $j:G\to H$ of $t$,
--
--   $$
--   \rho(g)(h)=j(g)h\,j(g)^{-1}.
--   $$
--
--   Consequently this action is independent of the section, and $(G,H,t,\rho)$ satisfies both crossed-module identities. Moreover
--
--   $$
--   \forall g,k\in G\quad\exists h\in H:\quad t(h)g=k,
--   $$
--
--   so all objects of the associated strict Gr-category are isomorphic. No section is assumed homomorphic, no splitting is assumed, and $H$ need not be abelian. This retains the final categorical conclusion on page 11.
-- source:
--   Hoàng Xuân Sính's Thesis: Categorifying Group Theory, arXiv:2308.05119v2, PDF p. 10, §4: section-independent central-extension example

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P06

namespace QAlgorithms.Papers.Independent.Intakenext100.P06

open CategoryTheory CategoryTheory.MonoidalCategory

open QAlgorithms.Papers.Independent.Gap48.P14

open QAlgorithms.Papers.Independent.Renew46.P18

universe u v u1 v1 w

attribute [local instance] QAlgorithms.Papers.Independent.Intakenext100.P06.singletonSymmetric

/-- Section 4, PDF pp. 10–11: an arbitrary central extension has a
section-independent conjugation action, satisfies both crossed-module
axioms, and its associated category has all objects isomorphic.
The sections are arbitrary set maps, never assumed homomorphisms. -/
theorem centralExtensionCrossedModule
    {C : Type u} {H : Type v} {G : Type w} [Group C] [Group H] [Group G]
    (i : C →* H) (t : H →* G) (hi : Function.Injective i)
    (hex : t.ker = i.range) (ht : Function.Surjective t)
    (hc : ∀ c : C, ∀ h : H, i c * h = h * i c) :
    ∃ rho : G →* MulAut H,
      (∀ j : G → H, (∀ g, t (j g) = g) →
        ∀ g h, rho g h = j g * h * (j g)⁻¹) ∧
      IsCrossedModule t rho ∧
      (∀ g k : G, ∃ h : H, t h * g = k) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P06
