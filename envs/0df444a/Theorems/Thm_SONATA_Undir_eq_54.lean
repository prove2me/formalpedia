-- Prove2me | Theorems.Thm_SONATA_Undir_eq_54
-- name    : SONATA.Undir.eq_54
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T19:17:53.700295+00:00
-- url     : https://prove2.me/theorems/1fc13280-dd49-49d8-8b8a-0337497a32e6
-- title:
--   (54), p. 21; proof App. A, pp. 34–35 — D^K(z) ≤ 𝒫(α, z)D^K(z) + ℛ(α, z) for every z in (51)
-- statement:
--   In the setting of Proposition 3.8 (standing assumptions, constants $L_i$ as in (1), a SONATA run with step size $\alpha\in(0,1]$, $\varepsilon_{\rm opt}$ with (34), $\varepsilon_x,\varepsilon_y>0$, and $z$ in (51)), for every $K=0,1,\dots$,
--   $$D^K(z)\le\mathcal P(\alpha,z)\,D^K(z)+\mathcal R(\alpha,z),$$
--   where $\mathcal P(\alpha,z)$ is (55),
--   $$\mathcal P(\alpha,z)=G_PG_XC_1\,4L_{\rm mx}^2\rho^2\alpha^2+(2G_PC_1+C_2)G_Y\,2L_{\rm mx}^2\rho^2\alpha^2+(2G_PC_1+C_2)G_Y\,8L_{\rm mx}^2\rho^2G_X\rho^2\alpha^2,$$
--   and $\mathcal R(\alpha,z)$ is the remainder computed in Appendix A,
--   $$\mathcal R(\alpha,z)=C_1\omega_p+(2C_1G_P+C_2)\omega_y+C_1G_P\,4L_{\rm mx}^2\omega_x+(2C_1G_P+C_2)G_Y\,8L_{\rm mx}^2\rho^2\omega_x.$$
--
--   Whenever $\mathcal P(\alpha,z)<1$ this bounds $D^K(z)$ uniformly in $K$, so $\|\mathbf d^\nu\|^2=O(z^\nu)$; Theorem 3.9 finds $\alpha$ and $z$ with $\mathcal P(\alpha,z)<1$.
-- source:
--   Sun, Daneshmand & Scutari, Distributed Optimization Based on Gradient-tracking Revisited, arXiv:1905.02637v2, p. 21, (54), (55) p. 22; proof and explicit ℛ in Appendix A, pp. 34–35

import Mathlib
import Definitions.Def_SONATA_Undir_Network
import Definitions.Def_SONATA_Undir_Setting
import Definitions.Def_SONATA_Undir_Chain

namespace SONATA.Undir

theorem eq_54
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
      let gp := GP σ η z
      let gx := GXY ρ εx z
      let gy := GXY ρ εy z
      let c1 := C1 μ (mutmn μt) (Dmx Dl Du) (Lmx Li)
      let c2 := C2 (mutmn μt)
      let wp := omegaP σ z (pgap f G xstar x 0)
      let wx := omegaXY ρ εx z (stackNormSq (perp (x 0)))
      let wy := omegaXY ρ εy z (stackNormSq (perp (y 0)))
      DK ≤ Pcal gp gx gy c1 c2 (Lmx Li) ρ α * DK + Rcal gp gy c1 c2 (Lmx Li) ρ wp wx wy := by sorry

end SONATA.Undir
