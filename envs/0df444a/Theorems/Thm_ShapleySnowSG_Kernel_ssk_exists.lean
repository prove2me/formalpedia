-- Prove2me | Theorems.Thm_ShapleySnowSG_Kernel_ssk_exists
-- name    : ShapleySnowSG.Kernel.ssk_exists
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T04:58:37.635764+00:00
-- url     : https://prove2.me/theorems/ba6314c3-9c31-4e65-bf38-c9d888f4425f
-- title:
--   §3.1, p. 14 — every matrix game (in particular each local game G^k(λ, v_λ)) admits a Shapley–Snow kernel
-- statement:
--   Let $G$ be a real $I\times J$ matrix game with $I$ and $J$ finite and nonempty. Then $G$ admits a Shapley–Snow kernel: there are subsets $\dot I\subset I$, $\dot J\subset J$ with $|\dot I|=|\dot J|$ such that the square sub-matrix $\dot G=G_{\dot I\times\dot J}$ satisfies $S(\mathrm{co}(\dot G))\neq0$ and the strategies
--   $$\dot x=\frac{\mathrm{co}(\dot G)}{S(\mathrm{co}(\dot G))}\mathbf 1,\qquad\dot y=\frac{{}^t\mathrm{co}(\dot G)}{S(\mathrm{co}(\dot G))}\mathbf 1,$$
--   completed with zeros, are optimal in $G$.
--
--   The paper applies this to every local game $\mathcal G^k(\lambda,v_\lambda)$ to define the reduced array $\dot D(\lambda)$; without it the main theorem would have no kernel to speak of.
--
--   **Formalization Note** Stated for an arbitrary matrix game, which is the content of "By Shapley and Snow [13]" in the source sentence; the local games are a special case.
-- source:
--   Attia & Oliu-Barton, Shapley–Snow kernels, multiparameter eigenvalue problems and stochastic games, arXiv:1810.08798v2, p. 14, §3.1 (first paragraph), citing Shapley and Snow [13]

import Mathlib
import Definitions.Def_ShapleySnowSG_Kernel_MatrixGame

namespace ShapleySnowSG.Kernel

open Matrix

/-- §3.1, p. 14 (by Shapley and Snow): every matrix game with nonempty finite action sets admits
a Shapley–Snow kernel `İ × J̇` with `|İ| = |J̇|`. -/
theorem ssk_exists {ι κ : Type*} [Fintype ι] [Fintype κ] [Nonempty ι] [Nonempty κ]
    (G : Matrix ι κ ℝ) :
    ∃ (s : ℕ) (r : Fin s ↪ ι) (c : Fin s ↪ κ), IsSSK G s r c := by sorry

end ShapleySnowSG.Kernel
