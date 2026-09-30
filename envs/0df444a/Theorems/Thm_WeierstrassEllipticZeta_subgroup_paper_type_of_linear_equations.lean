-- Prove2me | Theorems.Thm_WeierstrassEllipticZeta_subgroup_paper_type_of_linear_equations
-- name    : WeierstrassEllipticZeta.subgroup_paper_type_of_linear_equations
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-25T02:02:46.062777+00:00
-- url     : https://prove2.me/theorems/2b2807d7-d405-4fc5-af8a-15e9094dc944
-- title:
--   Lemma A.1: classify the linear exponential equation sets
-- statement:
--   Let H be a proper algebraic subgroup of any compatible Weierstrass Model. If its homogeneous equations agree with the exponential image of a complex vector subspace of C³, then H has one of the four equation sets in Lemma A.1: the identity, the full extension factor, the additive plane, or a nonconstant line in that plane. The proof includes the nonzero elliptic projection case and every compatible Model. The linear exponential equation description is an explicit hypothesis; its existence for an arbitrary connected algebraic subgroup remains a separate input.
-- source:
--   Senthil Kumar, https://doi.org/10.1017/S001309152610145X, Appendix A, the exponential map and Lemma A.1. This is a Senthil application result, not a result of Philippon’s paper.

import Definitions.Def_WeierstrassEllipticZeta_SubgroupLinearization
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open WeierstrassEllipticZeta WeierstrassEllipticZeta.PhilipponApplication PhilipponMultiplicity

theorem WeierstrassEllipticZeta.subgroup_paper_type_of_linear_equations
    (L : PeriodPair) (D : EllipticSigmaDifferentialData L)
    (S : Fin 5 → ℂ → ℂ)
    (hS : ∀ j, AnalyticOnNhd ℂ (S j) Set.univ)
    (hS_value : ∀ z : ℂ, z ∉ L.lattice → ∀ j : Fin 5,
      S j z = D.sigma z ^ 3 * ![1, L.weierstrassP z, L.derivWeierstrassP z,
        weierstrassZeta L z,
        L.derivWeierstrassP z * weierstrassZeta L z + 2 * L.weierstrassP z ^ 2] j)
    (hS_ne : ∀ z : ℂ, ∃ j : Fin 5, S j z ≠ 0)
    (M : Model S) (H : AlgebraicSubgroup M.group)
    (hproper : H.carrier ≠ Set.univ) (hlinear : M.HasLinearSubgroupEquations H) :
    M.HasPaperSubgroupType L H := by sorry
