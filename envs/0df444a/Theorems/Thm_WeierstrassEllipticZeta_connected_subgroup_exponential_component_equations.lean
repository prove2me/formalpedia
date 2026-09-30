-- Prove2me | Theorems.Thm_WeierstrassEllipticZeta_connected_subgroup_exponential_component_equations
-- name    : WeierstrassEllipticZeta.connected_subgroup_exponential_component_equations
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-25T03:17:43.487518+00:00
-- url     : https://prove2.me/theorems/ac043867-93ad-451c-bf0d-6f967d805225
-- title:
--   The analytic exponential component has the equations of the connected subgroup
-- statement:
--   For every proper Zariski-connected algebraic subgroup H in any compatible Weierstrass Model M, the exponential image of the analytic component of zero in M.exponentialPreimage H has exactly the bihomogeneous equations of H. This is the remaining algebraic density statement, including the identification for arbitrary Models. Zariski connectedness and norm-topological connectedness are different; the implication must be proved using algebraicity.
-- source:
--   Senthil Kumar, https://doi.org/10.1017/S001309152610145X, Appendix A, exponential maps and Lemma A.1. Supporting application geometry belongs to Senthil, not Philippon.

import Definitions.Def_WeierstrassEllipticZeta_ExponentialPreimage
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open WeierstrassEllipticZeta WeierstrassEllipticZeta.PhilipponApplication PhilipponMultiplicity

theorem WeierstrassEllipticZeta.connected_subgroup_exponential_component_equations
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
    M.HasParametricEquations H
      (fun v : connectedComponentIn (M.exponentialPreimage H) 0 =>
        exponentialCoordinates S v.val) := by sorry
