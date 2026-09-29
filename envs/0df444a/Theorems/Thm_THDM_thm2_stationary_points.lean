-- Prove2me | Theorems.Thm_THDM_thm2_stationary_points
-- name    : THDM.thm2_stationary_points
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-20T00:58:07.673778+00:00
-- url     : https://prove2.me/theorems/5d90a625-8a95-4f9c-81c0-8e96b464c941
-- title:
--   Theorem 2: classification of the stationary points of the THDM potential
-- statement:
--   **Theorem 2 of arXiv:hep-ph/0605184.** In the four-vector notation $\tilde K=(K_0,K)$, $\tilde\xi=(\xi_0,\xi)$, $\tilde E$, $\tilde g=\mathrm{diag}(1,-1,-1,-1)$, the stationary points of the potential $V=\tilde K^{\mathsf T}\tilde\xi+\tilde K^{\mathsf T}\tilde E\tilde K$ on its domain are given by:
--
--   - **(I a)** $\tilde K=\tilde K(0)$ if $\tilde f'(0)<0$, $K_0(0)>0$ and $\det\tilde E\neq0$;
--   - **(I b)** the solutions $\tilde K$ of (5.5) if $\det\tilde E=0$;
--   - **(II a)** $\tilde K=\tilde K(u)$ for those $u$ with $\det(\tilde E-u\tilde g)\neq0$, $\tilde f'(u)=0$ and $K_0(u)>0$;
--   - **(II b)** the solutions $\tilde K$ of (5.10) for those $u$ with $\det(\tilde E-u\tilde g)=0$;
--   - **(III)** $\tilde K=0$,
--
--   where $\tilde K(u)=-\tfrac12(\tilde E-u\tilde g)^{-1}\tilde\xi$ (5.11) and $\tilde f'$ is given by (5.17). Cases (I) are the stationary points in the interior $K_0>|K|$ of the domain, cases (II) those on its boundary $K_0=|K|>0$, where $u$ is the Lagrange multiplier, and (III) is the trivial configuration.
-- source:
--   M. Maniatis, A. von Manteuffel, O. Nachtmann, F. Nagel, 'Stability and Symmetry Breaking in the General Two-Higgs-Doublet Model', Eur. Phys. J. C 48 (2006) 805-823, arXiv:hep-ph/0605184v3, https://arxiv.org/abs/hep-ph/0605184, Sect. 5, p. 12, Theorem 2 (with eqs. 5.5-5.17)

import Definitions.Def_THDM_stationary
open scoped BigOperators
open Matrix

namespace THDM

theorem thm2_stationary_points
    (xi0 : ℝ) (xi : Fin 3 → ℝ) (eta00 : ℝ) (eta : Fin 3 → ℝ)
    (E : Matrix (Fin 3) (Fin 3) ℝ) (hE : E.IsSymm) (x : Idx → ℝ) :
    IsStatPoint xi0 xi eta00 eta E x ↔
      (-- (I a)
        (RegT eta00 eta E 0 ∧ fTPrime xi0 xi eta00 eta E 0 < 0 ∧
          0 < comp0 (KT xi0 xi eta00 eta E 0) ∧ x = KT xi0 xi eta00 eta E 0) ∨
      -- (I b)
        (¬ RegT eta00 eta E 0 ∧ 0 < comp0 x ∧ 0 < mink x ∧
          ET eta00 eta E *ᵥ x = (-(1 / 2 : ℝ)) • xiT xi0 xi) ∨
      -- (II a)
        (∃ u : ℝ, RegT eta00 eta E u ∧ fTPrime xi0 xi eta00 eta E u = 0 ∧
          0 < comp0 (KT xi0 xi eta00 eta E u) ∧ x = KT xi0 xi eta00 eta E u) ∨
      -- (II b)
        (∃ u : ℝ, ¬ RegT eta00 eta E u ∧ 0 < comp0 x ∧ mink x = 0 ∧
          (ET eta00 eta E - u • gT) *ᵥ x = (-(1 / 2 : ℝ)) • xiT xi0 xi) ∨
      -- (III)
        x = 0) := by sorry

end THDM
