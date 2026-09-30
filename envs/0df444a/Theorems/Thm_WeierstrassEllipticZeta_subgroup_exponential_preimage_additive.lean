-- Prove2me | Theorems.Thm_WeierstrassEllipticZeta_subgroup_exponential_preimage_additive
-- name    : WeierstrassEllipticZeta.subgroup_exponential_preimage_additive
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-25T03:17:38.179674+00:00
-- url     : https://prove2.me/theorems/0284aeb4-b703-4e32-91d8-eac554f6c4b5
-- title:
--   Exponential equation preimages are additive in every model
-- statement:
--   For the sigma-normalized entire Weierstrass coordinates and every compatible Model M, the inverse image in C³ of the projective closure of an actual algebraic subgroup H is an additive subgroup. This is the remaining algebraic group compatibility statement for arbitrary Models. It must be derived from the actual regular group laws, dense curve and coordinate data; additivity is not a field of Model or of the exponentialPreimage definition. No connectedness or properness is required.
-- source:
--   Senthil Kumar, https://doi.org/10.1017/S001309152610145X, Appendix A, exponential maps and Lemma A.1. Supporting application geometry belongs to Senthil, not Philippon.

import Definitions.Def_WeierstrassEllipticZeta_ExponentialPreimage
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open WeierstrassEllipticZeta WeierstrassEllipticZeta.PhilipponApplication PhilipponMultiplicity

theorem WeierstrassEllipticZeta.subgroup_exponential_preimage_additive
    (L : PeriodPair) (D : EllipticSigmaDifferentialData L)
    (S : Fin 5 → ℂ → ℂ)
    (hS : ∀ j, AnalyticOnNhd ℂ (S j) Set.univ)
    (hS_value : ∀ z : ℂ, z ∉ L.lattice → ∀ j : Fin 5,
      S j z = D.sigma z ^ 3 * ![1, L.weierstrassP z, L.derivWeierstrassP z,
        weierstrassZeta L z,
        L.derivWeierstrassP z * weierstrassZeta L z + 2 * L.weierstrassP z ^ 2] j)
    (hS_ne : ∀ z : ℂ, ∃ j : Fin 5, S j z ≠ 0)
    (M : Model S) (H : AlgebraicSubgroup M.group) :
    ∃ K : AddSubgroup (Fin 3 → ℂ), (K : Set (Fin 3 → ℂ)) = M.exponentialPreimage H := by sorry
