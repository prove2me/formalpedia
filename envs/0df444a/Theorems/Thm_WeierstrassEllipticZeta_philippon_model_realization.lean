-- Prove2me | Theorems.Thm_WeierstrassEllipticZeta_philippon_model_realization
-- name    : WeierstrassEllipticZeta.philippon_model_realization
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-23T21:59:28.121275+00:00
-- url     : https://prove2.me/theorems/41f11d41-7dcb-4a6f-a464-93802a926110
-- title:
--   Algebraic-group realization of the Weierstrass curve
-- statement:
--   Let $L$ be a complex period pair with lattice $\Lambda$, and let $D$ be its elliptic sigma differential data. Suppose the five functions $S_j$ are analytic on a neighborhood of every complex point, have no common zero, and, off $\Lambda$, satisfy
--   $$
--   (S_0,S_1,S_2,S_3,S_4)
--   =\sigma^3(1,\wp,\wp',\zeta,\wp'\zeta+2\wp^2).
--   $$
--   Then these specific functions admit a `PhilipponApplication.Model`.
--
--   Concretely, the assertion requires actual locally closed projective commutative groups of Hilbert dimensions one and two, with regular group operations; a compatible renaming of the seven polynomial variables; an injective, Zariski dense additive parameterization; and an actual one-dimensional local analytic subgroup with the prescribed coordinate pullbacks at every parameter. Its generated image must equal the image of the complex parameterization. Bihomogeneous polynomial vanishing must agree with vanishing of the specified raw coordinates. No multiplicity or subgroup-degree estimate is included in this conclusion.
--
--   This is a **proved application theorem in Senthil**. Philippon’s full-paper goal retains its original scope. Constructing the model includes proving its regularity, Hilbert dimensions, density, analytic lift compatibility, and generated-image identity. The existing analytic quotient presentation alone does not prove this statement.
-- source:
--   Senthil Kumar, Appendix A, application geometry, https://doi.org/10.1017/S001309152610145X; Philippon (1986), Theorem 2.1 and Lemma 3.4, https://numdam.org/articles/10.24033/bsmf.2060/. Explicit application lemma in Senthil; not a numbered theorem in Philippon.

import Definitions.Def_WeierstrassEllipticZeta_PhilipponModel

set_option autoImplicit false
open WeierstrassEllipticZeta WeierstrassEllipticZeta.PhilipponApplication
open PhilipponMultiplicity

theorem WeierstrassEllipticZeta.philippon_model_realization    (L : PeriodPair) (D : EllipticSigmaDifferentialData L)
    (S : Fin 5 → ℂ → ℂ)
    (hS : ∀ j, AnalyticOnNhd ℂ (S j) Set.univ)
    (hS_value : ∀ z : ℂ, z ∉ L.lattice → ∀ j : Fin 5,
      S j z = D.sigma z ^ 3 * ![1, L.weierstrassP z, L.derivWeierstrassP z,
        weierstrassZeta L z,
        L.derivWeierstrassP z * weierstrassZeta L z + 2 * L.weierstrassP z ^ 2] j)
    (hS_ne : ∀ z : ℂ, ∃ j : Fin 5, S j z ≠ 0) :
    Nonempty (Model S) := by sorry
