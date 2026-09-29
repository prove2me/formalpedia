-- Prove2me | Theorems.Thm_Rep_dualTwist_smooth
-- name    : Rep.dualTwist_smooth
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.865614+00:00
-- url     : https://prove2.me/theorems/fe103b73-bfce-5ac4-b461-da2d3a2a1a3d
-- title:
--   Smoothness of the twisted dual of a smooth representation
-- statement:
--   Let $k$ be a field, $G$ a group, and $r \colon G \to \operatorname{Aut}_{\mathbb{Q}}(\overline{\mathbb{Q}})$ a group homomorphism into the $\mathbb{Q}$-algebra automorphisms of `AlgebraicClosure ℚ`. Let $M$ be a $k$-linear representation of $G$, finite-dimensional over $k$, with action $\rho =$ `M.ρ`, and let $\chi \colon G \to k^{\times}$ be a character. Assume two hypotheses. First, $M$ is smooth for $r$: for every $m \in M$ there is an intermediate field $F$ of $\overline{\mathbb{Q}}/\mathbb{Q}$, finite-dimensional over $\mathbb{Q}$, such that $\rho(s)m = m$ whenever $r(s)$ lies in the fixing subgroup of $F$ (i.e. $r(s)$ fixes $F$ pointwise). Second, $\chi$ has a level: there is such a finite $F$ with $\chi(s) = 1$ whenever $r(s)$ fixes $F$ pointwise. The conclusion is that the representation `M.dualTwist χ`, namely the $k$-dual of $M$ with $s$ acting as $\chi(s)$ times the transpose of $\rho(s^{-1})$, is again smooth for $r$: for every $f$ in it there is a finite intermediate field $F$ of $\overline{\mathbb{Q}}/\mathbb{Q}$ with $(\chi(s)\cdot {}^{t}\rho(s^{-1}))(f) = f$ for all $s$ with $r(s)$ fixing $F$ pointwise.
--
--   This is the statement that the twisted contragredient $M^{\vee}(\chi)$ of a smooth finite-dimensional representation is smooth, for a character $\chi$ trivial on some level subgroup. It supplies the smoothness hypothesis on the dual side in the duality statements for Selmer-type group cohomology, and is used by the results asserting bijectivity of the comparison map $\theta$ for twisted duals.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Rep_dualTwist_smooth.lean

import Mathlib
import Definitions.Def_GroupCohomology_Selmer

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory

theorem Rep.dualTwist_smooth {k G : Type u} [Field k] [Group G]
    (r : G →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (M : Rep.{u} k G) [FiniteDimensional k M] (χ : G →* kˣ)
    (hsm : ∀ m : M, ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
      ∀ s, r s ∈ F.fixingSubgroup → M.ρ s m = m)
    (hχ : ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
      ∀ s, r s ∈ F.fixingSubgroup → χ s = 1) :
    ∀ f : M.dualTwist χ, ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
      ∀ s, r s ∈ F.fixingSubgroup → (M.dualTwist χ).ρ s f = f := by sorry
