-- Prove2me | Theorems.Thm_Rep_finrank_invariants_res_dualTwist_eq
-- name    : Rep.finrank_invariants_res_dualTwist_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.865614+00:00
-- url     : https://prove2.me/theorems/bad6fa77-910e-5673-9ff2-78bebfa93fc0
-- title:
--   Restriction commutes with the cyclotomic twist of the dual
-- statement:
--   Let $p$ be a prime, let $H$ be a group and let $r \colon H \to \mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ be a group homomorphism, where $\overline{\mathbb{Q}}$ is the algebraic closure `AlgebraicClosure ℚ` and the Galois group is its group of $\mathbb{Q}$-algebra automorphisms. Let $M$ be a representation of this Galois group over $\mathbb{Z}/p$ whose underlying module is finite-dimensional over $\mathbb{Z}/p$. Here `cycloChar p` is the homomorphism from the Galois group to $(\mathbb{Z}/p)^{\times}$ given by the modular cyclotomic character attached to the $p$-th roots of unity in $\overline{\mathbb{Q}}$, and for a representation $A$ over a group $G$ and a character $\chi \colon G \to k^{\times}$, the twisted dual `A.dualTwist χ` is the representation on the dual module $A^{\vee}$ sending $g$ to $\chi(g)$ times the contragredient action $f \mapsto f \circ A.\rho(g^{-1})$. The assertion is the equality of $\mathbb{Z}/p$-dimensions of two spaces of $H$-invariants: that of the restriction along $r$ of $M^{\vee}(\mathrm{cycloChar}\,p)$, and that of the twisted dual of the restriction of $M$ along $r$ by the character $\mathrm{cycloChar}\,p \circ r$.
--
--   A compatibility between restriction along a homomorphism of groups and the formation of the cyclotomically twisted dual: the two spellings differ only in whether the inversion in the contragredient action is taken before or after restriction, so they have the same underlying module and the same action, and in particular the same invariants. It serves as the interface between statements formulated with a global twist followed by restriction and those formulated with the twist of an already restricted module, and is used in [`groupCohomology.greenbergWiles_eq_unramifiedMenu_extArithLoc`](thm.html#groupCohomology.greenbergWiles_eq_unramifiedMenu_extArithLoc).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Rep_finrank_invariants_res_dualTwist_eq.lean

import Mathlib
import Definitions.Def_GroupCohomology_ContinuousUnramified
import Definitions.Def_DualSelmer_ExtConditions
import Definitions.Def_ExtCitation_KummerBridge

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open CategoryTheory Module groupCohomology ExtCitation

theorem Rep.finrank_invariants_res_dualTwist_eq
    {p : ℕ} [Fact p.Prime] {H : Type} [Group H]
    (r : H →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    (M : Rep (ZMod p) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) [FiniteDimensional (ZMod p) M] :
    finrank (ZMod p) (Rep.res r (M.dualTwist (cycloChar p))).ρ.invariants
      = finrank (ZMod p) ((Rep.res r M).dualTwist ((cycloChar p).comp r)).ρ.invariants := by sorry
