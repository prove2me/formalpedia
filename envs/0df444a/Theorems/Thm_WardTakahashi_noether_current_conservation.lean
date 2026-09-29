-- Prove2me | Theorems.Thm_WardTakahashi_noether_current_conservation
-- name    : WardTakahashi.noether_current_conservation
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-27T21:16:17.418984+00:00
-- url     : https://prove2.me/theorems/77f22440-bda8-4e14-ae8f-b06d13512550
-- title:
--   Lattice Noether theorem: $\sum_x \delta_x S = 0$ for a $U(1)$-invariant action
-- statement:
--   Let $S:\mathbb C^N\to\mathbb R$ be real-differentiable and invariant under global phase rotations, $S(e^{i\theta}\varphi)=S(\varphi)$ for all $\theta\in\mathbb R$, $\varphi\in\mathbb C^N$. Then for every configuration $\varphi$,
--   $$\sum_{x}\delta_xS(\varphi)=0,\qquad \delta_xS(\varphi)=DS(\varphi)\,[g_x\varphi],$$
--   where $g_x\varphi$ is the infinitesimal phase rotation of site $x$ alone.
--
--   This is the lattice form of Noether's theorem: $\delta_xS$ is the divergence of the Noether current at $x$, and global invariance makes its total vanish (classical current conservation).
-- source:
--   Wikipedia, "Ward–Takahashi identity" (revision oldid=1374751657), https://en.wikipedia.org/w/index.php?title=Ward%E2%80%93Takahashi_identity&oldid=1374751657 ; section "Derivation in the path integral formulation" (finite-dimensional lattice model)

import Mathlib
import Definitions.Def_WardTakahashi_LatticeU1

open MeasureTheory Complex

namespace WardTakahashi

theorem noether_current_conservation {N : ℕ} (S : FieldConfig N → ℝ)
    (hS : Differentiable ℝ S) (hinv : IsU1Invariant S) (φ : FieldConfig N) :
    ∑ x, localVar x S φ = 0 := by sorry

end WardTakahashi
