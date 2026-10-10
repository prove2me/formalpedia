-- Prove2me | Theorems.Thm_SONATA_Undir_proposition_3_6
-- name    : SONATA.Undir.proposition_3_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T19:17:09.345667+00:00
-- url     : https://prove2.me/theorems/a15f77c4-7209-4e0c-9c9a-3ab6baee572e
-- title:
--   Proposition 3.6, p. 19 — ‖d^ν‖² ≤ (6/μ)((D_mx/μ̃_mn + 1)² + 4L²_mx/μ̃²_mn)p^ν + (3/μ̃²_mn)‖y_⊥^ν‖²
-- statement:
--   Under the standing assumptions of §3.3 and constants $L_i$ as in (1), let $(\mathbf x^\nu,\mathbf y^\nu,\hat{\mathbf x}^\nu)$ be a run of SONATA with step size $\alpha\in(0,1]$. Then for every $\nu$,
--   $$\|\mathbf d^\nu\|^2\le\frac6\mu\bigg(\Big(\frac{D_{\rm mx}}{\tilde\mu_{\rm mn}}+1\Big)^2+\frac{4L_{\rm mx}^2}{\tilde\mu_{\rm mn}^2}\bigg)p^\nu+\frac{3}{\tilde\mu_{\rm mn}^2}\|\mathbf y_\perp^\nu\|^2.$$
--
--   The step length is bounded back by the optimality gap and the tracker disagreement, which closes the loop formed by Propositions 3.4 and 3.5.
-- source:
--   Sun, Daneshmand & Scutari, Distributed Optimization Based on Gradient-tracking Revisited, arXiv:1905.02637v2, p. 19, Proposition 3.6, (47); proof pp. 19–20

import Mathlib
import Definitions.Def_SONATA_Undir_Network
import Definitions.Def_SONATA_Undir_Setting

namespace SONATA.Undir

theorem proposition_3_6
    {m d : ℕ} {K O : Set (E d)} {f : Fin m → E d → ℝ} {G : E d → ℝ} {μ L : ℝ}
    {ft : Fin m → E d → E d → ℝ} {μt Lt Dl Du : Fin m → ℝ} {Gr : SimpleGraph (Fin m)}
    {W : Matrix (Fin m) (Fin m) ℝ} {xstar : E d}
    (hS : Standing K O f G μ L ft μt Lt Dl Du Gr W xstar)
    {μi Li : Fin m → ℝ} (h1 : Eq1 K f μi Li)
    {α : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1) {x y xh : ℕ → Stack m d}
    (hrun : IsRun K f G ft W α x y xh) :
    ∀ ν, stackNormSq (dir x xh ν) ≤
      6 / μ * ((Dmx Dl Du / mutmn μt + 1) ^ 2 + 4 * Lmx Li ^ 2 / mutmn μt ^ 2) * pgap f G xstar x ν
        + 3 / mutmn μt ^ 2 * stackNormSq (perp (y ν)) := by sorry

end SONATA.Undir
