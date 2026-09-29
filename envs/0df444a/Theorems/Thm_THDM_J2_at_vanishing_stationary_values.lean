-- Prove2me | Theorems.Thm_THDM_J2_at_vanishing_stationary_values
-- name    : THDM.J2_at_vanishing_stationary_values
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-20T00:51:00.530991+00:00
-- url     : https://prove2.me/theorems/ea4f3dd5-2118-4dc9-869d-8fca27ef2bfd
-- title:
--   Equations (4.42)-(4.44): $J_2$ at the stationary points where $J_4$ vanishes
-- statement:
--   **Equations (4.42)-(4.44) of arXiv:hep-ph/0605184.**
--
--   Let $u_i\in I$ be a point with $f(u_i)=0$, so that the corresponding stationary points of $J_4$ have $J_4=0$ and the stability question is decided by $J_2$ there. If $u_i$ is not an eigenvalue of $E$, the corresponding stationary point is unique and
--   $$J_2(k)=g(u_i),\qquad g(u)=\xi_0-\xi^{\mathsf T}(E-u)^{-1}\eta .$$
--   If $u_i$ is an eigenvalue of $E$, there is a whole family of exceptional solutions $k$, and the infimum of $J_2$ over that family is
--   $$g(u_i)-|\xi_\perp(u_i)|\sqrt{f'(u_i)},$$
--   where $\xi_\perp(u_i)$ is the orthogonal projection of $\xi$ onto the eigenspace of $E$ for the eigenvalue $u_i$. These two formulas are exactly the quantities whose signs enter conditions (4.45) and (4.46) of Theorem 1.
-- source:
--   M. Maniatis, A. von Manteuffel, O. Nachtmann, F. Nagel, 'Stability and Symmetry Breaking in the General Two-Higgs-Doublet Model', Eur. Phys. J. C 48 (2006) 805-823, arXiv:hep-ph/0605184v3, https://arxiv.org/abs/hep-ph/0605184, Sect. 4, p. 9, eqs. (4.40)-(4.44)

import Definitions.Def_THDM_stationary
open scoped BigOperators
open Matrix

namespace THDM

theorem J2_at_vanishing_stationary_values
    (xi0 : ℝ) (xi : Fin 3 → ℝ) (eta00 : ℝ) (eta : Fin 3 → ℝ)
    (E : Matrix (Fin 3) (Fin 3) ℝ) (hE : E.IsSymm)
    (u : ℝ) (hu : u ∈ Iset eta00 eta E) (hf : fVal eta00 eta E u = 0) :
    (Reg E u → ∀ k : Fin 3 → ℝ,
        (E - u • (1 : Matrix (Fin 3) (Fin 3) ℝ)) *ᵥ k = -eta →
        J2 xi0 xi k = gVal xi0 xi eta E u) ∧
    (¬ Reg E u → ∀ p : Fin 3 → ℝ, IsEigenProj E u xi p →
        IsGLB {v : ℝ | ∃ k : Fin 3 → ℝ, dot3 k k = 1 ∧
                  (E - u • (1 : Matrix (Fin 3) (Fin 3) ℝ)) *ᵥ k = -eta ∧ v = J2 xi0 xi k}
              (gVal xi0 xi eta E u - norm3 p * Real.sqrt (fPrimeVal eta E u))) := by sorry

end THDM
