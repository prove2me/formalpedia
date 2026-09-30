-- Prove2me | Theorems.Thm_WeierstrassEllipticZeta_philippon_subgroup_degree_profile
-- name    : WeierstrassEllipticZeta.philippon_subgroup_degree_profile
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-23T21:59:25.582782+00:00
-- url     : https://prove2.me/theorems/b463c1b2-e1be-4e50-a352-be00a3730ba0
-- title:
--   Proper-subgroup Hilbert degrees in the Weierstrass extension
-- statement:
--   Use the period pair, sigma differential data, and entire functions
--   $$S=\sigma^3(1,\wp,\wp',\zeta,\wp'\zeta+2\wp^2)$$
--   off the period lattice $\Lambda$, with no common zero. Let $M$ be any compatible Philippon model of these functions. For every proper connected Zariski closed algebraic subgroup $H$ of its group, put $K=\varphi^{-1}(H)$, an integer submodule of $\mathbb C$.
--
--   At least one of the following alternatives holds:
--
--   1. $K=\{0\}$ and $\mathcal H(H;m,n)\ge1$ for every positive integer pair $m,n$.
--   2. $K\subseteq\Lambda$ and $\mathcal H(H;m,n)\ge m$ for every positive integer pair $m,n$.
--
--   The branch is chosen before $m,n$. Both branches may hold. The degree form is the factorial-normalized top part of the actual quotient Hilbert polynomial of the embedded subgroup’s vanishing ideal, not an assigned numerical degree. Under its general definition the polynomial is zero if an eventual Hilbert polynomial does not exist, so its required existence and positivity must be established in proving this statement.
--
--   This is a **proved geometric application theorem in Senthil**. It combines the extension’s proper-subgroup projection classification with the nonempty-variety degree bound and the stronger mixed-degree bound when projection onto the additive factor is surjective. It has no finite sample, contact order, polynomial vanishing hypothesis, or multiplicity conclusion.
-- source:
--   Senthil Kumar, Appendix A, application geometry, https://doi.org/10.1017/S001309152610145X; Philippon (1986), Theorem 2.1 and Lemma 3.4, https://numdam.org/articles/10.24033/bsmf.2060/. Explicit application lemma in Senthil; not a numbered theorem in Philippon.

import Definitions.Def_WeierstrassEllipticZeta_PhilipponModel

set_option autoImplicit false
open WeierstrassEllipticZeta WeierstrassEllipticZeta.PhilipponApplication
open PhilipponMultiplicity

theorem WeierstrassEllipticZeta.philippon_subgroup_degree_profile    (L : PeriodPair) (D : EllipticSigmaDifferentialData L)
    (S : Fin 5 → ℂ → ℂ)
    (hS : ∀ j, AnalyticOnNhd ℂ (S j) Set.univ)
    (hS_value : ∀ z : ℂ, z ∉ L.lattice → ∀ j : Fin 5,
      S j z = D.sigma z ^ 3 * ![1, L.weierstrassP z, L.derivWeierstrassP z,
        weierstrassZeta L z,
        L.derivWeierstrassP z * weierstrassZeta L z + 2 * L.weierstrassP z ^ 2] j)
    (hS_ne : ∀ z : ℂ, ∃ j : Fin 5, S j z ≠ 0)
    (M : Model S) (H : AlgebraicSubgroup M.group)
    (hH : H.IsConnected) (hproper : H.carrier ≠ Set.univ) :
    ((M.pullbackSubmodule H = ⊥) ∧
      ∀ m n : ℕ, 1 ≤ m → 1 ≤ n →
        1 ≤ hilbertDegreeForm M.group H.carrier ![m, n]) ∨
    ((M.pullbackSubmodule H ≤ L.lattice) ∧
      ∀ m n : ℕ, 1 ≤ m → 1 ≤ n →
        (m : ℝ) ≤ hilbertDegreeForm M.group H.carrier ![m, n]) := by sorry
