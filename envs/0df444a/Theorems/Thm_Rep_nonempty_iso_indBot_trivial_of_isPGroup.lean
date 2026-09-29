-- Prove2me | Theorems.Thm_Rep_nonempty_iso_indBot_trivial_of_isPGroup
-- name    : Rep.nonempty_iso_indBot_trivial_of_isPGroup
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.865614+00:00
-- url     : https://prove2.me/theorems/4dacf6b9-8e11-5a34-a293-bf860624be0b
-- title:
--   Induced from the trivial subgroup when pV=0 and H₁ vanishes
-- statement:
--   Let $p$ be a natural number assumed prime, and let $P$ be a finite group which is a $p$-group in the sense of `IsPGroup p P`. Let $V$ be a type carrying an additive commutative group structure and let $\rho$ be a representation of $P$ on $V$ over $\mathbb{Z}$, i.e. an action of $P$ by automorphisms of $V$ for the canonical $\mathbb{Z}$-module structure. Assume that $V$ is $p$-torsion, in the sense that $(p : \mathbb{Z}) \cdot x = 0$ for every $x \in V$, and that the first group homology object $H_1$ of the associated object `Rep.of ρ` of $\mathrm{Rep}(\mathbb{Z}, P)$ is a zero object of the relevant category. The conclusion is that there exists a $\mathbb{Z}$-module $M$ (an object of `ModuleCat ℤ`) together with an isomorphism, in the category of $\mathbb{Z}$-linear representations of $P$, between `Rep.of ρ` and the representation `indBot` of the trivial representation of $P$ on $M$; here `indBot A` is the induction along the inclusion of the trivial subgroup $\bot \le P$ of the restriction of $A$ to $\bot$, so that the target is $\mathbb{Z}[P] \otimes_{\mathbb{Z}} M$ with $P$ acting by translation on the group-ring factor. Existence of the isomorphism is asserted in the `Nonempty` form.
--
--   This is the classical statement that a $p$-torsion module over a finite $p$-group whose first homology vanishes is induced from the trivial subgroup, equivalently free over $\mathbb{F}_p[P]$ (as in Serre's treatment of the cohomology of $p$-groups). It is used in the proof of [`Rep.isZero_tateCohomology_ihom_of_isPGroup`](thm.html#Rep.isZero_tateCohomology_ihom_of_isPGroup), within the dimension-shifting machinery for Tate cohomology.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Rep_nonempty_iso_indBot_trivial_of_isPGroup.lean

import Mathlib
import Definitions.Def_GroupCohomology_TateCohomology
import Definitions.Def_GroupCohomology_TateDimensionShift

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
universe u
open CategoryTheory Rep MonoidalCategory

theorem Rep.nonempty_iso_indBot_trivial_of_isPGroup {P : Type} [Group P] [Fintype P] {p : ℕ} [Fact p.Prime]
    (hP : IsPGroup p P) (V : Type) [AddCommGroup V] (ρ : Representation ℤ P V)
    (hp : ∀ x : V, (p : ℤ) • x = 0) (hN : CategoryTheory.Limits.IsZero (groupHomology (Rep.of ρ) 1)) :
    ∃ M : ModuleCat ℤ, Nonempty (Rep.of ρ ≅ (Rep.trivial ℤ P M).indBot) := by sorry
