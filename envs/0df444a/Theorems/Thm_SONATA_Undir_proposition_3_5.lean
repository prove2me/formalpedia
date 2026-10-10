-- Prove2me | Theorems.Thm_SONATA_Undir_proposition_3_5
-- name    : SONATA.Undir.proposition_3_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T19:17:01.842998+00:00
-- url     : https://prove2.me/theorems/a0a163ed-56a0-4c1e-b48c-ae86e64a1dc2
-- title:
--   Proposition 3.5, p. 19 — ‖x_⊥^{ν+1}‖ ≤ ρ‖x_⊥^ν‖ + αρ‖d^ν‖ and ‖y_⊥^{ν+1}‖ ≤ ρ‖y_⊥^ν‖ + 2L_mxρ‖x_⊥^ν‖ + αL_mxρ‖d^ν‖
-- statement:
--   Under the standing assumptions of §3.3 and constants $L_i$ as in (1), let $(\mathbf x^\nu,\mathbf y^\nu,\hat{\mathbf x}^\nu)$ be a run of SONATA with step size $\alpha\in(0,1]$ and $\rho=\sigma(\widehat{\mathbf W}-\mathbf J)$ as in (26). Then for every $\nu$,
--   $$\|\mathbf x_\perp^{\nu+1}\|\le\rho\|\mathbf x_\perp^\nu\|+\alpha\rho\|\mathbf d^\nu\|,\qquad(46\mathrm a)$$
--   $$\|\mathbf y_\perp^{\nu+1}\|\le\rho\|\mathbf y_\perp^\nu\|+2L_{\rm mx}\rho\|\mathbf x_\perp^\nu\|+\alpha L_{\rm mx}\rho\|\mathbf d^\nu\|,\qquad(46\mathrm b)$$
--   with Euclidean norms of stacked vectors.
--
--   The consensus errors contract at rate $\rho$ up to the step $\mathbf d^\nu$; these are the second link of the chain.
-- source:
--   Sun, Daneshmand & Scutari, Distributed Optimization Based on Gradient-tracking Revisited, arXiv:1905.02637v2, p. 19, Proposition 3.5, (46a)–(46b)

import Mathlib
import Definitions.Def_SONATA_Undir_Network
import Definitions.Def_SONATA_Undir_Setting

namespace SONATA.Undir

theorem proposition_3_5
    {m d : ℕ} {K O : Set (E d)} {f : Fin m → E d → ℝ} {G : E d → ℝ} {μ L : ℝ}
    {ft : Fin m → E d → E d → ℝ} {μt Lt Dl Du : Fin m → ℝ} {Gr : SimpleGraph (Fin m)}
    {W : Matrix (Fin m) (Fin m) ℝ} {xstar : E d}
    (hS : Standing K O f G μ L ft μt Lt Dl Du Gr W xstar)
    {μi Li : Fin m → ℝ} (h1 : Eq1 K f μi Li)
    {α : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1) {x y xh : ℕ → Stack m d}
    (hrun : IsRun K f G ft W α x y xh) :
    ∀ ν,
      stackNorm (perp (x (ν + 1))) ≤
          rho W * stackNorm (perp (x ν)) + α * rho W * stackNorm (dir x xh ν) ∧
      stackNorm (perp (y (ν + 1))) ≤
          rho W * stackNorm (perp (y ν)) + 2 * Lmx Li * rho W * stackNorm (perp (x ν))
            + α * Lmx Li * rho W * stackNorm (dir x xh ν) := by sorry

end SONATA.Undir
