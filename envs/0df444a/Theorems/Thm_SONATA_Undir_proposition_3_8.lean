-- Prove2me | Theorems.Thm_SONATA_Undir_proposition_3_8
-- name    : SONATA.Undir.proposition_3_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T19:17:44.56506+00:00
-- url     : https://prove2.me/theorems/8533413d-4dfe-457a-bbe5-c0b6218e7428
-- title:
--   Proposition 3.8, p. 21 — the transformed inequalities (50a)–(50d) for every z in (51)
-- statement:
--   Under the standing assumptions of §3.3 and constants $L_i$ as in (1), let $(\mathbf x^\nu,\mathbf y^\nu,\hat{\mathbf x}^\nu)$ be a run of SONATA with step size $\alpha\in(0,1]$. Let $\varepsilon_{\rm opt}$ satisfy (34), let $\varepsilon_x,\varepsilon_y>0$, and let $P^K(z)$, $X_\perp^K(z)$, $Y_\perp^K(z)$, $D^K(z)$ be the transformation (49), $S^K(z)=\max_{\nu=0,\dots,K}|s^\nu|z^{-\nu}$, applied to $\{p^\nu\}$, $\{\|\mathbf x_\perp^\nu\|^2\}$, $\{\|\mathbf y_\perp^\nu\|^2\}$, $\{\|\mathbf d^\nu\|^2\}$. Then for every $K=0,1,\dots$ and every
--   $$z\in\big(\max\{\sigma(\alpha),\rho^2(1+\varepsilon_x),\rho^2(1+\varepsilon_y)\},\,1\big),\qquad(51)$$
--   the following hold, with $G_P,G_X,G_Y,\omega_p,\omega_x,\omega_y,C_1,C_2$ as in (52a)–(52d):
--   $$P^K(z)\le G_P(\alpha,z)\big(4L_{\rm mx}^2X_\perp^K(z)+2Y_\perp^K(z)\big)+\omega_p,\qquad(50\mathrm a)$$
--   $$X_\perp^K(z)\le G_X(z)\,\rho^2\alpha^2D^K(z)+\omega_x,\qquad(50\mathrm b)$$
--   $$Y_\perp^K(z)\le G_Y(z)\,8L_{\rm mx}^2\rho^2X_\perp^K(z)+G_Y(z)\,2L_{\rm mx}^2\rho^2\alpha^2D^K(z)+\omega_y,\qquad(50\mathrm c)$$
--   $$D^K(z)\le C_1P^K(z)+C_2Y_\perp^K(z).\qquad(50\mathrm d)$$
--
--   These are the four arrows of the small-gain loop of Figure 1, uniform in the horizon $K$.
--
--   **Formalization Note.** $C_2=4/\tilde\mu_{\rm mn}^2$ as printed in (52d), although (47) gives the smaller coefficient $3/\tilde\mu_{\rm mn}^2$; (50d) holds with either. The local `let`s only name the quantities of (49) and (52).
-- source:
--   Sun, Daneshmand & Scutari, Distributed Optimization Based on Gradient-tracking Revisited, arXiv:1905.02637v2, p. 21, Proposition 3.8, (49)–(52d)

import Mathlib
import Definitions.Def_SONATA_Undir_Network
import Definitions.Def_SONATA_Undir_Setting
import Definitions.Def_SONATA_Undir_Chain

namespace SONATA.Undir

theorem proposition_3_8
    {m d : ℕ} {K O : Set (E d)} {f : Fin m → E d → ℝ} {G : E d → ℝ} {μ L : ℝ}
    {ft : Fin m → E d → E d → ℝ} {μt Lt Dl Du : Fin m → ℝ} {Gr : SimpleGraph (Fin m)}
    {W : Matrix (Fin m) (Fin m) ℝ} {xstar : E d}
    (hS : Standing K O f G μ L ft μt Lt Dl Du Gr W xstar)
    {μi Li : Fin m → ℝ} (h1 : Eq1 K f μi Li)
    {α : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1) {x y xh : ℕ → Stack m d}
    (hrun : IsRun K f G ft W α x y xh) :
    ∀ (N : ℕ) (εopt εx εy z : ℝ), Cond34 (mutmn μt) (Dlmn Dl) α εopt → 0 < εx → 0 < εy →
      max (sigmaA μ (mutmn μt) (Dlmn Dl) (Dmx Dl Du) α εopt)
          (max (rho W ^ 2 * (1 + εx)) (rho W ^ 2 * (1 + εy))) < z → z < 1 →
      let σ := sigmaA μ (mutmn μt) (Dlmn Dl) (Dmx Dl Du) α εopt
      let η := etaA μ (mutmn μt) (Dlmn Dl) (Dmx Dl Du) α εopt
      let ρ := rho W
      let PK := trans (pgap f G xstar x) N z
      let XK := trans (fun ν => stackNormSq (perp (x ν))) N z
      let YK := trans (fun ν => stackNormSq (perp (y ν))) N z
      let DK := trans (fun ν => stackNormSq (dir x xh ν)) N z
      PK ≤ GP σ η z * (4 * Lmx Li ^ 2 * XK + 2 * YK) + omegaP σ z (pgap f G xstar x 0) ∧
      XK ≤ GXY ρ εx z * ρ ^ 2 * α ^ 2 * DK + omegaXY ρ εx z (stackNormSq (perp (x 0))) ∧
      YK ≤ GXY ρ εy z * (8 * Lmx Li ^ 2 * ρ ^ 2) * XK
          + GXY ρ εy z * (2 * Lmx Li ^ 2 * ρ ^ 2 * α ^ 2) * DK
          + omegaXY ρ εy z (stackNormSq (perp (y 0))) ∧
      DK ≤ C1 μ (mutmn μt) (Dmx Dl Du) (Lmx Li) * PK + C2 (mutmn μt) * YK := by sorry

end SONATA.Undir
