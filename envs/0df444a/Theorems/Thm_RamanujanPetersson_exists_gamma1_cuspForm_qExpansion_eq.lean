-- Prove2me | Theorems.Thm_RamanujanPetersson_exists_gamma1_cuspForm_qExpansion_eq
-- name    : RamanujanPetersson.exists_gamma1_cuspForm_qExpansion_eq
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-11-13T01:30:12.294215+00:00
-- url     : https://prove2.me/theorems/92ba19bb-55b3-4236-95f0-74f937001cdb
-- title:
--   Width transfer: a cusp form on a congruence subgroup has the same expansion as a cusp form on some $\Gamma_1(M)$
-- statement:
--   Let $\Gamma\subseteq \mathrm{SL}_2(\mathbb Z)$ be a congruence subgroup, $k\in\mathbb Z$, and $f\in S_k(\Gamma)$ a cusp form. Let $h$ be the strict width of $\Gamma$ at $\infty$ and $f(\tau)=\sum_{n\ge0}a_n e^{2\pi i n\tau/h}$ its $q_h$-expansion. Then there are $M\ge1$ and a cusp form $g\in S_k(\Gamma_1(M))$ whose $q$-expansion has exactly the same coefficients:
--
--   $$g(\tau)=\sum_{n\ge0} a_n e^{2\pi i n\tau}.$$
--
--   Role: reduces the Ramanujan–Petersson bound for an arbitrary congruence subgroup and the expansion at its strict width to the case of $\Gamma_1(M)$ with the standard $q$-expansion.
--
--   **Formalization Note**: $h$ is Mathlib's `strictWidthInfty`; the coefficients are those of Mathlib's `qExpansion`.
-- source:
--   F. Diamond, J. Shurman, A First Course in Modular Forms (GTM 228), Springer 2005, https://doi.org/10.1007/978-0-387-27226-9, Section 1.2, p. 13 (conjugating $\Gamma(N)$ by $\mathrm{diag}(N,1)$ gives a group containing $\Gamma_1(N^2)$, so $f(N\tau)$ is a form on $\Gamma_1(N^2)$)

import Mathlib
open UpperHalfPlane Filter Asymptotics MatrixGroups ModularForm

namespace RamanujanPetersson

theorem exists_gamma1_cuspForm_qExpansion_eq (Γ : Subgroup SL(2, ℤ))
    (hΓ : CongruenceSubgroup.IsCongruenceSubgroup Γ) (k : ℤ)
    (f : CuspForm (Γ : Subgroup (GL (Fin 2) ℝ)) k) :
    ∃ M : ℕ, 0 < M ∧ ∃ g : CuspForm ((CongruenceSubgroup.Gamma1 M : Subgroup SL(2, ℤ)) :
        Subgroup (GL (Fin 2) ℝ)) k,
      ∀ n : ℕ, (qExpansion (Γ : Subgroup (GL (Fin 2) ℝ)).strictWidthInfty f).coeff n =
        (qExpansion 1 g).coeff n := by sorry

end RamanujanPetersson
