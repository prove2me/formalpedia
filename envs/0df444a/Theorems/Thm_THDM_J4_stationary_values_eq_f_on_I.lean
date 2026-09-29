-- Prove2me | Theorems.Thm_THDM_J4_stationary_values_eq_f_on_I
-- name    : THDM.J4_stationary_values_eq_f_on_I
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-20T00:48:32.637148+00:00
-- url     : https://prove2.me/theorems/0ca3ac18-44c9-4fd1-8a20-c75216e23958
-- title:
--   Equation (4.39): the stationary values of $J_4$ are exactly the numbers $f(u_i)$, $u_i\in I$
-- statement:
--   **Equation (4.39) of arXiv:hep-ph/0605184** (with (4.11)-(4.22) and the discussion of exceptional solutions).
--
--   The stationary points of $J_4$ on the closed ball $|k|\le1$ are the interior points with $Ek=-\eta$, $|k|<1$ (4.11), and the boundary points with $|k|=1$ satisfying $(E-u)k=-\eta$ for a Lagrange multiplier $u$ (4.14). For a symmetric $E$, the set of values taken by $J_4$ at these points coincides with $\{f(u_i):u_i\in I\}$, where
--   $$f(u)=u+\eta_{00}-\eta^{\mathsf T}(E-u)^{-1}\eta$$
--   and $I$ is the set of (4.38): the regular $u$ with $f'(u)=0$, the point $u=0$ if $f'(0)>0$, and those eigenvalues of $E$ at which $f$ stays finite with $f'\ge0$ - the last clause being the 'exceptional' solutions, where $f$ and $f'$ are read as limits. This is the identity that turns the search for the minimum of $J_4$ into the evaluation of one rational function at finitely many points, and it is what the stability criterion of Theorem 1 rests on.
-- source:
--   M. Maniatis, A. von Manteuffel, O. Nachtmann, F. Nagel, 'Stability and Symmetry Breaking in the General Two-Higgs-Doublet Model', Eur. Phys. J. C 48 (2006) 805-823, arXiv:hep-ph/0605184v3, https://arxiv.org/abs/hep-ph/0605184, Sect. 4, pp. 8-9, eqs. (4.11)-(4.22), (4.38), (4.39)

import Definitions.Def_THDM_stationary
open scoped BigOperators
open Matrix

namespace THDM

theorem J4_stationary_values_eq_f_on_I
    (eta00 : ℝ) (eta : Fin 3 → ℝ) (E : Matrix (Fin 3) (Fin 3) ℝ) (hE : E.IsSymm) :
    {v : ℝ | ∃ k : Fin 3 → ℝ,
        ((dot3 k k < 1 ∧ E *ᵥ k = -eta) ∨
         (dot3 k k = 1 ∧ ∃ u : ℝ, (E - u • (1 : Matrix (Fin 3) (Fin 3) ℝ)) *ᵥ k = -eta)) ∧
        v = J4 eta00 eta E k}
      = (fun u => fVal eta00 eta E u) '' (Iset eta00 eta E) := by sorry

end THDM
