-- Prove2me | Theorems.Thm_WeierstrassEllipticZeta_philippon_connected_subgroup_classification
-- name    : WeierstrassEllipticZeta.philippon_connected_subgroup_classification
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-25T01:21:21.633451+00:00
-- url     : https://prove2.me/theorems/69401802-1b76-4b93-8808-541f22218e58
-- title:
--   Lemma A.1: connected subgroups in the compatible Weierstrass model
-- statement:
--   Let L be a period lattice, with the entire sigma coordinates specified in Appendix A, and let M be any compatible algebraic-group realization. Every proper connected algebraic subgroup H has the same bihomogeneous equations as one of the loci in Lemma A.1:
--
--   1. The identity point.
--   2. The extension factor {0} × G₂.
--   3. The additive plane Gₐ × i(Gₐ).
--   4. A nonconstant additive line in that plane.
--
--   In coordinates these are the point, ([1:0],p) for p in G₂, ([1:t],[0:0:1:0:ρ+u]), and ([1:at],[0:0:1:0:ρ+bt]), with (a,b) nonzero. The offset ρ allows the chosen origin in the vertical chart. This states the geometric classification through equality of homogeneous equations, so it is weaker than equality of embedded subgroup carriers. It contains no assumed Hilbert-degree formula, curve-intersection bound, or multiplicity estimate. The quantifier over all compatible models is retained.
-- source:
--   Senthil Kumar, https://doi.org/10.1017/S001309152610145X, Appendix A, Lemma A.1 and the four subgroup cases in the proof of Proposition A.1. This is a Senthil application result, not a result of Philippon’s paper.

import Definitions.Def_WeierstrassEllipticZeta_SubgroupCoordinateCases
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open WeierstrassEllipticZeta WeierstrassEllipticZeta.PhilipponApplication PhilipponMultiplicity

theorem WeierstrassEllipticZeta.philippon_connected_subgroup_classification
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
    M.HasPaperSubgroupType L H := by sorry
