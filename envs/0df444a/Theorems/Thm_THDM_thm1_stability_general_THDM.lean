-- Prove2me | Theorems.Thm_THDM_thm1_stability_general_THDM
-- name    : THDM.thm1_stability_general_THDM
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-20T00:58:57.413845+00:00
-- url     : https://prove2.me/theorems/361a5d8b-6dc2-4f1b-9644-1d63a0408e57
-- title:
--   Theorem 1: complete stability criterion for the general two-Higgs-doublet potential
-- statement:
--   **Theorem 1 of arXiv:hep-ph/0605184**, the goal of this mission: a complete characterisation of the stability of the general THDM potential
--   $$V=\xi_0K_0+\xi^{\mathsf T}K+\eta_{00}K_0^2+2K_0\eta^{\mathsf T}K+K^{\mathsf T}EK .$$
--
--   If the potential has only the quadratic term ($V_4\equiv0$) it is stable for $\xi_0>|\xi|$, marginally stable for $\xi_0=|\xi|$, and unstable for $\xi_0<|\xi|$.
--
--   Suppose now $V_4\not\equiv0$, and construct $f$ (4.19), $f'$ (4.20), $g$ (4.40) and the set $I$ (4.38) of at most ten values of $u$. Then:
--
--   (i) if $f(u_i)>0$ for all $u_i\in I$, the potential is stable in the strong sense (4.4), i.e. $J_4>0$ on $|k|\le1$;
--
--   (ii) if $f(u_i)<0$ for at least one $u_i\in I$, the potential is unstable;
--
--   (iii) if $f(u_i)\ge0$ for all $u_i\in I$ and $f(u_i)=0$ for at least one $u_i\in I$, one considers $g$: the potential is stable in the weak sense (4.7) provided that, at every $u_i\in I$ with $f(u_i)=0$,
--   $$g(u_i)>0\ \text{ if } u_i \text{ is not an eigenvalue of } E, \qquad g(u_i)-|\xi_\perp(u_i)|\sqrt{f'(u_i)}>0 \ \text{ otherwise},$$
--   while if the corresponding quantity is $<0$ for at least one such $u_i$ the potential is unstable. (Equality is the marginal case, which this criterion does not decide and which is covered by the separate marginal-stability milestone.)
-- source:
--   M. Maniatis, A. von Manteuffel, O. Nachtmann, F. Nagel, 'Stability and Symmetry Breaking in the General Two-Higgs-Doublet Model', Eur. Phys. J. C 48 (2006) 805-823, arXiv:hep-ph/0605184v3, https://arxiv.org/abs/hep-ph/0605184, Sect. 4, p. 10, Theorem 1 (with eqs. 4.4, 4.7, 4.19, 4.20, 4.38, 4.40, 4.45, 4.46)

import Definitions.Def_THDM_stationary
open scoped BigOperators
open Matrix

namespace THDM

theorem thm1_stability_general_THDM
    (xi0 : ℝ) (xi : Fin 3 → ℝ) (eta00 : ℝ) (eta : Fin 3 → ℝ)
    (E : Matrix (Fin 3) (Fin 3) ℝ) (hE : E.IsSymm) :
    (V4Trivial eta00 eta E →
        ((norm3 xi < xi0 → Stable xi0 xi eta00 eta E) ∧
         (xi0 = norm3 xi → MarginalCase xi0 xi eta00 eta E ∧ Stable xi0 xi eta00 eta E) ∧
         (xi0 < norm3 xi → ¬ Stable xi0 xi eta00 eta E))) ∧
    (¬ V4Trivial eta00 eta E →
      ((∀ u ∈ Iset eta00 eta E, 0 < fVal eta00 eta E u) →
          StrongStable eta00 eta E) ∧
      ((∃ u ∈ Iset eta00 eta E, fVal eta00 eta E u < 0) →
          ¬ Stable xi0 xi eta00 eta E) ∧
      (((∀ u ∈ Iset eta00 eta E, 0 ≤ fVal eta00 eta E u) ∧
        (∃ u ∈ Iset eta00 eta E, fVal eta00 eta E u = 0)) →
        ((∀ u ∈ Iset eta00 eta E, fVal eta00 eta E u = 0 →
            (Reg E u → 0 < gVal xi0 xi eta E u) ∧
            (¬ Reg E u → ∀ p : Fin 3 → ℝ, IsEigenProj E u xi p →
                0 < gVal xi0 xi eta E u - norm3 p * Real.sqrt (fPrimeVal eta E u))) →
              WeakStable xi0 xi eta00 eta E) ∧
        ((∃ u ∈ Iset eta00 eta E, fVal eta00 eta E u = 0 ∧
            ((Reg E u ∧ gVal xi0 xi eta E u < 0) ∨
             (¬ Reg E u ∧ ∃ p : Fin 3 → ℝ, IsEigenProj E u xi p ∧
                gVal xi0 xi eta E u - norm3 p * Real.sqrt (fPrimeVal eta E u) < 0))) →
              ¬ Stable xi0 xi eta00 eta E))) := by sorry

end THDM
