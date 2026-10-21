-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P02_stoneRepresentation
-- name    : QAlgorithms.Papers.Independent.Renew46.P02.stoneRepresentation
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T19:50:55.210238+00:00
-- url     : https://prove2.me/theorems/45f994bb-3acf-4223-bc62-bf9ea7f881ff
-- title:
--   Theorem 7.13: Stone representation theorem
-- statement:
--   Let $B$ be any Boolean algebra and $Z$ its set of nonzero ring homomorphisms onto the two-element Boolean ring. Equivalently, $Z$ is the set of unital bounded lattice homomorphisms $B\to\{0,1\}$. Define $\widehat a=\{z\in Z:z(a)=1\}$. Then the prescribed map $a\mapsto\widehat a$ is injective and
--
--   $$
--   \widehat0=\varnothing,\quad \widehat1=Z,\quad
--   \widehat{a\vee b}=\widehat a\cup\widehat b,\quad
--   \widehat{a\wedge b}=\widehat a\cap\widehat b,\quad
--   \widehat{a^c}=Z\setminus\widehat a.
--   $$
--
--   It is therefore an injective unital Boolean homomorphism into the power set of this specified $Z$. For the trivial Boolean algebra $Z$ is empty; no nontriviality hypothesis is added.
-- source:
--   Abelian von Neumann algebras, measure algebras and L^\infty-spaces, arXiv:2108.06406v2, PDF p. 33, Theorem 7.13

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P02

noncomputable section

open MeasureTheory Set

open scoped ENNReal Topology CompactlySupported

namespace QAlgorithms.Papers.Independent.Renew46.P02

universe u v

/-- Theorem 7.13, PDF p.33. The exact Stone map is injective and preserves
all unital Boolean operations; no arbitrary representation is substituted. -/
theorem stoneRepresentation (B : Type u) [BooleanAlgebra B] :
    Function.Injective (stoneSet (B := B)) ∧
    stoneSet (⊥ : B) = ∅ ∧ stoneSet (⊤ : B) = Set.univ ∧
    (∀ a b : B, stoneSet (a ⊔ b) = stoneSet a ∪ stoneSet b) ∧
    (∀ a b : B, stoneSet (a ⊓ b) = stoneSet a ∩ stoneSet b) ∧
    (∀ a : B, stoneSet aᶜ = (stoneSet a)ᶜ) := by sorry

end QAlgorithms.Papers.Independent.Renew46.P02

end
