-- Prove2me | Theorems.Thm_WeierstrassEllipticZeta_subgroup_degree_profile_of_paper_type
-- name    : WeierstrassEllipticZeta.subgroup_degree_profile_of_paper_type
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-25T01:21:47.484666+00:00
-- url     : https://prove2.me/theorems/399fd1a5-3f33-463b-9a9f-7c8b319898f5
-- title:
--   Subgroup degree profile from the cases of Lemma A.1
-- statement:
--   Let M be any compatible realization of the entire Weierstrass coordinates, and let H be an algebraic subgroup whose homogeneous equations have one of the four forms in Lemma A.1. Then either the preimage of H under the modeled curve is {0} and its Hilbert degree is at least 1, or that preimage is contained in the period lattice and its Hilbert degree at (m,n) is at least m, for every m,n≥1.
--
--   All numerical and intersection assertions are conclusions. The exact degrees used are 1 for a point, 6n² for the extension factor, 2mn for the additive plane, and m, n, or m+n for a line. The statement applies to every compatible model; it does not replace the model with a specially chosen realization.
-- source:
--   Senthil Kumar, https://doi.org/10.1017/S001309152610145X, Appendix A, Lemma A.1 and the four subgroup cases in the proof of Proposition A.1. This is a Senthil application result, not a result of Philippon’s paper.

import Definitions.Def_WeierstrassEllipticZeta_SubgroupCoordinateCases
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open WeierstrassEllipticZeta WeierstrassEllipticZeta.PhilipponApplication PhilipponMultiplicity

theorem WeierstrassEllipticZeta.subgroup_degree_profile_of_paper_type
    (L : PeriodPair) (D : EllipticSigmaDifferentialData L)
    (S : Fin 5 → ℂ → ℂ)
    (hS : ∀ j, AnalyticOnNhd ℂ (S j) Set.univ)
    (hS_value : ∀ z : ℂ, z ∉ L.lattice → ∀ j : Fin 5,
      S j z = D.sigma z ^ 3 * ![1, L.weierstrassP z, L.derivWeierstrassP z,
        weierstrassZeta L z,
        L.derivWeierstrassP z * weierstrassZeta L z + 2 * L.weierstrassP z ^ 2] j)
    (hS_ne : ∀ z : ℂ, ∃ j : Fin 5, S j z ≠ 0)
    (M : Model S) (H : AlgebraicSubgroup M.group)
    (hclass : M.HasPaperSubgroupType L H) :
    (M.pullbackSubmodule H = ⊥ ∧
      ∀ m n : ℕ, 1 ≤ m → 1 ≤ n → 1 ≤ hilbertDegreeForm M.group H.carrier ![m, n]) ∨
    (M.pullbackSubmodule H ≤ L.lattice ∧
      ∀ m n : ℕ, 1 ≤ m → 1 ≤ n → (m : ℝ) ≤ hilbertDegreeForm M.group H.carrier ![m, n]) := by sorry
