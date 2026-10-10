-- Prove2me | Theorems.Thm_SONATA_Undir_eq_19
-- name    : SONATA.Undir.eq_19
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T19:17:12.130223+00:00
-- url     : https://prove2.me/theorems/00347675-2399-4d9a-b5fd-8a7e5f475b35
-- title:
--   (19), p. 13 — the tracking invariant ȳ^ν = (1/m) Σᵢ ∇fᵢ(xᵢ^ν) for every ν
-- statement:
--   Under the standing assumptions of §3.3 (Assumptions A–D, (15) and an optimal solution $\mathbf x^\star$), let $(\mathbf x^\nu,\mathbf y^\nu,\hat{\mathbf x}^\nu)_{\nu\ge0}$ be a run of SONATA (Algorithm 1) with step size $\alpha\in(0,1]$. Then for every $\nu=0,1,\dots$,
--   $$\bar{\mathbf y}^\nu=\frac1m\sum_{i=1}^m\mathbf y_i^\nu=\frac1m\sum_{i=1}^m\nabla f_i(\mathbf x_i^\nu)=\overline{\nabla\mathbf f}^\nu.$$
--
--   The average of the trackers equals the average of the local gradients at every iteration. This is what makes $\mathbf y_i^\nu$ a proxy for $\nabla F(\mathbf x_i^\nu)$ once consensus is reached, and it enters Lemma 3.3 and Proposition 3.6.
-- source:
--   Sun, Daneshmand & Scutari, Distributed Optimization Based on Gradient-tracking Revisited, arXiv:1905.02637v2, p. 13, (19) (with (17)–(18))

import Mathlib
import Definitions.Def_SONATA_Undir_Network
import Definitions.Def_SONATA_Undir_Setting

namespace SONATA.Undir

theorem eq_19
    {m d : ℕ} {K O : Set (E d)} {f : Fin m → E d → ℝ} {G : E d → ℝ} {μ L : ℝ}
    {ft : Fin m → E d → E d → ℝ} {μt Lt Dl Du : Fin m → ℝ} {Gr : SimpleGraph (Fin m)}
    {W : Matrix (Fin m) (Fin m) ℝ} {xstar : E d}
    (hS : Standing K O f G μ L ft μt Lt Dl Du Gr W xstar)
    {α : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1) {x y xh : ℕ → Stack m d}
    (hrun : IsRun K f G ft W α x y xh) :
    ∀ ν, avg (y ν) = (m : ℝ)⁻¹ • ∑ i, gradient (f i) (x ν i) := by sorry

end SONATA.Undir
