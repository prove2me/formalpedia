-- Prove2me | Theorems.Thm_WeierstrassEllipticZeta_philippon_obstruction_codimension_one
-- name    : WeierstrassEllipticZeta.philippon_obstruction_codimension_one
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-25T21:36:59.869288+00:00
-- url     : https://prove2.me/theorems/32f7a647-f906-42e0-9aed-6d18e398f9a7
-- title:
--   Proper connected Weierstrass subgroups have analytic codimension one
-- statement:
--   Let $L$ be a period lattice, let $\sigma$ be normalized entire sigma data, and let $S$ be its five entire Weierstrass projective coordinates. In every compatible geometric realization $M$, each proper connected algebraic subgroup $H$ satisfies
--   $$
--   \operatorname{codim}_{M.A}(H)=1.
--   $$
--   The codimension is computed from the derivatives of the subgroup's actual homogeneous vanishing ideal. The statement applies to every compatible model and retains the original coordinate and subgroup hypotheses of the Senthil application.
-- source:
--   Senthil Kumar, https://doi.org/10.1017/S001309152610145X, Appendix A, Lemma A.1 subgroup classification and Theorem A.2 application; Philippon (1986), §2 p. 358, analytic codimension. Application-specific transversality lemma in Senthil; the full general Philippon contact theorem remains separate.

import Definitions.Def_WeierstrassEllipticZeta_SubgroupCoordinateCases
set_option autoImplicit false
open WeierstrassEllipticZeta WeierstrassEllipticZeta.PhilipponApplication PhilipponMultiplicity

theorem WeierstrassEllipticZeta.philippon_obstruction_codimension_one
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
    analyticCodimension M.A H.carrier = 1 := by sorry
