-- Prove2me | Theorems.Thm_WeierstrassEllipticZeta_connected_subgroup_linear_equations
-- name    : WeierstrassEllipticZeta.connected_subgroup_linear_equations
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-25T02:02:48.385544+00:00
-- url     : https://prove2.me/theorems/c9b17ee0-784c-40d7-b9e0-3d559884c3fe
-- title:
--   Connected subgroups admit linear exponential equations
-- statement:
--   For the entire Weierstrass coordinates and any compatible Model M, every proper connected algebraic subgroup H has the same bihomogeneous polynomial equations as the exponential image of a complex vector subspace V of C³. The exponential coordinates are [1,v₀; S₀(v₁),S₁(v₁),S₂(v₁),S₃(v₁)+v₂S₀(v₁),S₄(v₁)+v₂S₂(v₁)]. This is the geometric linearization input used by the proof of Lemma A.1. It asserts equality of projective closures through equations, rather than equality of point sets, and includes the identification required for every compatible Model. Existence of this vector subspace is not proved by the coordinate saturation argument. No subgroup classification, degree bound, or multiplicity estimate is a hypothesis.
-- source:
--   Senthil Kumar, https://doi.org/10.1017/S001309152610145X, Appendix A, the exponential map and Lemma A.1. This is a Senthil application result, not a result of Philippon’s paper.

import Definitions.Def_WeierstrassEllipticZeta_SubgroupLinearization
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open WeierstrassEllipticZeta WeierstrassEllipticZeta.PhilipponApplication PhilipponMultiplicity

theorem WeierstrassEllipticZeta.connected_subgroup_linear_equations
    (L : PeriodPair) (D : EllipticSigmaDifferentialData L)
    (S : Fin 5 → ℂ → ℂ)
    (hS : ∀ j, AnalyticOnNhd ℂ (S j) Set.univ)
    (hS_value : ∀ z : ℂ, z ∉ L.lattice → ∀ j : Fin 5,
      S j z = D.sigma z ^ 3 * ![1, L.weierstrassP z, L.derivWeierstrassP z,
        weierstrassZeta L z,
        L.derivWeierstrassP z * weierstrassZeta L z + 2 * L.weierstrassP z ^ 2] j)
    (hS_ne : ∀ z : ℂ, ∃ j : Fin 5, S j z ≠ 0)
    (M : Model S) (H : AlgebraicSubgroup M.group)
    (hH : H.IsConnected) (hproper : H.carrier ≠ Set.univ) :
    M.HasLinearSubgroupEquations H := by sorry
