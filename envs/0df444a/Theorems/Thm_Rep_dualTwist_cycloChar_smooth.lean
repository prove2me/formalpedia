-- Prove2me | Theorems.Thm_Rep_dualTwist_cycloChar_smooth
-- name    : Rep.dualTwist_cycloChar_smooth
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.865614+00:00
-- url     : https://prove2.me/theorems/45604662-2dcf-5b97-83ef-7f16acee4e47
-- title:
--   Smoothness of the cyclotomic dual twist of a mod p Galois module
-- statement:
--   Let $p$ be a prime and let $M$ be a representation of the absolute Galois group $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$, realised as the group of field automorphisms of $\mathrm{AlgebraicClosure}\ \mathbb{Q}$ over $\mathbb{Q}$, on a finite-dimensional $\mathbb{Z}/p$-vector space. Assume $M$ is smooth in the pointwise sense: for every vector $m \in M$ there is an intermediate field $F$ of $\overline{\mathbb{Q}}/\mathbb{Q}$, finite-dimensional over $\mathbb{Q}$, such that every $s$ in the fixing subgroup of $F$ satisfies $M.\rho\, s\, m = m$. The conclusion is the same pointwise smoothness for the representation $M.\mathrm{dualTwist}\ (\mathrm{cycloChar}\ p)$, that is, for the linear dual of $M$ carried by the contragredient action $f \mapsto f \circ M.\rho\, (g^{-1})$ multiplied by the scalar $\mathrm{cycloChar}\ p\, g \in (\mathbb{Z}/p)^{\times}$, where $\mathrm{cycloChar}\ p$ is the mod $p$ cyclotomic character obtained from the modular cyclotomic character of $\overline{\mathbb{Q}}$: for each functional $f$ in this twisted dual there exists an intermediate field $F$, finite over $\mathbb{Q}$, whose fixing subgroup fixes $f$ for the twisted action.
--
--   This is the statement that the cyclotomic (Tate) dual of a smooth finite $\mathbb{F}_p$-Galois module is again smooth, i.e. again a discrete Galois module. It serves to supply the smoothness hypothesis at the dual module for results on Poitou–Tate duality and local–global Selmer computations, which invoke it when passing from $M$ to $M^{\vee}(\chi_p)$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Rep_dualTwist_cycloChar_smooth.lean

import Mathlib
import Definitions.Def_GroupCohomology_ContinuousUnramified
import Definitions.Def_DualSelmer_ExtConditions
import Definitions.Def_ExtCitation_KummerBridge

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open CategoryTheory Module groupCohomology ExtCitation

theorem Rep.dualTwist_cycloChar_smooth
    {p : ℕ} [Fact p.Prime] (M : Rep (ZMod p) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    [FiniteDimensional (ZMod p) M]
    (hsm : ∀ m : M, ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
      ∀ s ∈ F.fixingSubgroup, M.ρ s m = m) :
    ∀ f : M.dualTwist (cycloChar p), ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
      ∀ s ∈ F.fixingSubgroup, (M.dualTwist (cycloChar p)).ρ s f = f := by sorry
