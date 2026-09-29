-- Prove2me | Theorems.Thm_WeierstrassCurve_exists_variableChange_map_subtype_eq_and_smul_eq_of_isUnit_discriminant
-- name    : WeierstrassCurve.exists_variableChange_map_subtype_eq_and_smul_eq_of_isUnit_discriminant
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.985064+00:00
-- url     : https://prove2.me/theorems/55d3f5a0-95bd-5103-88a9-b334163e1c79
-- title:
--   Isomorphisms of unit-discriminant models descend to the valuation ring
-- statement:
--   Let $L$ be a field and let $A$ be a valuation subring of $L$, so that `A.subtype` is the inclusion ring homomorphism $A \to L$. Let $E_1$ and $E_2$ be Weierstrass curves over $A$, i.e. tuples of coefficients $(a_1,a_2,a_3,a_4,a_6)$ in $A$, and suppose that the discriminants $\Delta(E_1)$ and $\Delta(E_2)$, computed from these coefficients in $A$, are units of $A$. Let $C$ be an admissible change of variables over $L$, that is a tuple $(u,r,s,t)$ with $u \in L^{\times}$ and $r,s,t \in L$, and assume that $C$ carries the base change of $E_1$ along $A \to L$ to the base change of $E_2$, i.e. $C \bullet (E_1 \otimes_A L) = E_2 \otimes_A L$ for the standard action of the group of variable changes on Weierstrass curves. The conclusion is that there exists a change of variables $C_0$ over $A$, i.e. with $u \in A^{\times}$ and $r,s,t \in A$, whose image under the map induced by $A \to L$ equals $C$, and which already satisfies $C_0 \bullet E_1 = E_2$ as Weierstrass curves over $A$.
--
--   This is the uniqueness assertion for good integral models: two Weierstrass models over a valuation ring with unit discriminant that become isomorphic over the fraction field are isomorphic over the ring, and every such isomorphism of generic fibres has integral coefficients with unit leading entry, hence reduces. It is used in the comparison of the reductions of two integral models with the same $j$-invariant over a valued field.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_exists_variableChange_map_subtype_eq_and_smul_eq_of_isUnit_discriminant.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem WeierstrassCurve.exists_variableChange_map_subtype_eq_and_smul_eq_of_isUnit_discriminant {L : Type*} [Field L] (A : ValuationSubring L) (E₁ E₂ : WeierstrassCurve A) (h₁ : IsUnit E₁.Δ) (h₂ : IsUnit E₂.Δ) (C : WeierstrassCurve.VariableChange L) (hC : C • E₁.map A.subtype = E₂.map A.subtype) : ∃ C₀ : WeierstrassCurve.VariableChange A, C₀.map A.subtype = C ∧ C₀ • E₁ = E₂ := by sorry
