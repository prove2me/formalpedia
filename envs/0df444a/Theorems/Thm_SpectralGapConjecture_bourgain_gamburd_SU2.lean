-- Prove2me | Theorems.Thm_SpectralGapConjecture_bourgain_gamburd_SU2
-- name    : SpectralGapConjecture.bourgain_gamburd_SU2
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-13T02:02:54.380981+00:00
-- url     : https://prove2.me/theorems/ac4fec51-51a1-4f00-ad54-7c6d7ec73a26
-- title:
--   Bourgain–Gamburd: spectral gap for free subgroups of $SU(2)$ with algebraic entries
-- statement:
--   Let $\mu_2$ be the normalized Haar measure on $SU(2)$ and let $n \ge 2$. Let $g_1,\dots,g_n\in SU(2)$ satisfy:
--
--   1. **algebraic entries up to simultaneous conjugation:** there is $V \in SU(2)$ such that every entry of every matrix $Vg_jV^{-1}$ is an algebraic number;
--   2. **freeness:** $g_1,\dots,g_n$ freely generate a free group, i.e. the homomorphism from the free group $F_n$ on $n$ letters to $SU(2)$ sending the $j$-th letter to $g_j$ is injective.
--
--   Then the Hecke operator $(z_g f)(x) = \sum_{j=1}^{n}\bigl(f(g_jx) + f(g_j^{-1}x)\bigr)$ has a spectral gap on $L^2(SU(2),\mu_2)$:
--   $$
--   \lambda_1(z_g) < 2n .
--   $$
--
--   This gives spectral gap for an explicit, countable family of tuples; that family is Haar-null, so it does not settle the conjecture.
--
--   **Formalization Note.** Conjugation is by an element of $SU(2)$; algebraic means algebraic over $\mathbb Q$.
-- source:
--   J. Bourgain, A. Gamburd, On the spectral gap for finitely-generated subgroups of SU(2), Invent. Math. 171 (2008) 83–121, https://doi.org/10.1007/s00222-007-0072-z, main theorem; cited in Wikipedia, "Spectral gap conjecture" (https://en.wikipedia.org/wiki/Spectral_gap_conjecture), section Progress, and in Fisher, arXiv:math/0601050, p. 1

import Mathlib
import Definitions.Def_SpectralGapConjecture_HeckeSU

open MeasureTheory

namespace SpectralGapConjecture

theorem bourgain_gamburd_SU2 (n : ℕ) (hn : 2 ≤ n) (g : Fin n → SU 2)
    (halg : ∃ V : SU 2, ∀ j a b,
      IsAlgebraic ℚ (((V * g j * V⁻¹ : SU 2) : Matrix (Fin 2) (Fin 2) ℂ) a b))
    (hfree : Function.Injective (FreeGroup.lift g)) :
    HasSpectralGap (haarSU 2) g := by sorry

end SpectralGapConjecture
