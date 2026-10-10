-- Prove2me | Theorems.Thm_SONATA_Push_prop_4_3
-- name    : SONATA.Push.prop_4_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T20:14:42.19097+00:00
-- url     : https://prove2.me/theorems/0299cf42-7067-4d49-b1d0-3638247cc333
-- title:
--   Proposition 4.3, p. 30 — ‖d^ν‖² is bounded by p_φ^ν and ‖y_{φ,⊥}^ν‖²
-- statement:
--   In the standing setting (Assumptions A, B′, C, E, the constants (15), a solution $x^\star$), let $\mu_i\ge0$, $L_i>0$ satisfy (1). For every run of Algorithm 3 with step size $\alpha\in(0,1]$ and every $\nu$,
--   $$\|d^\nu\|^2\le\frac{6}{\mu\,\phi_{lb}}\Big(\Big(\frac{D_{\rm mx}}{\tilde\mu_{\rm mn}}+1\Big)^2+\frac{4L_{\rm mx}^2}{\tilde\mu_{\rm mn}^2}\Big)p_\phi^\nu+\frac{3}{\tilde\mu_{\rm mn}^2}\|y^\nu_{\phi,\perp}\|^2,$$
--   where $\|d^\nu\|^2=\sum_i\|\hat x_i^\nu-x_i^\nu\|^2$ and $\phi_{lb}=c_\ell^{2(m-1)B}$.
--
--   The step lengths are controlled by the optimality gap and the tracking consensus error; this closes the loop between Proposition 4.1 and the consensus estimates.
-- source:
--   Sun, Daneshmand & Scutari, Distributed Optimization Based on Gradient-tracking Revisited, arXiv:1905.02637v2, p. 30, Proposition 4.3, (84)

import Mathlib
import Definitions.Def_SONATA_Push_Network

namespace SONATA.Push

/-- Proposition 4.3 (p. 30):
`‖d^ν‖² ≤ (6/(μ φ_lb)) ((D_mx/μ̃_mn + 1)² + 4 L²_mx/μ̃²_mn) p_φ^ν + (3/μ̃²_mn) ‖y_{φ,⊥}^ν‖²`. -/
theorem prop_4_3
    {m d : ℕ} (K O : Set (SONATA.Undir.E d)) (f : Fin m → SONATA.Undir.E d → ℝ) (G : SONATA.Undir.E d → ℝ) (μ L : ℝ)
    (ft : Fin m → SONATA.Undir.E d → SONATA.Undir.E d → ℝ) (μt Lt Dl Du : Fin m → ℝ) (xstar : SONATA.Undir.E d)
    (Edges : ℕ → Fin m → Fin m → Prop) (B : ℕ) (C : ℕ → Matrix (Fin m) (Fin m) ℝ) (cl : ℝ)
    (hP : ProblemHyp K O f G μ L ft μt Lt Dl Du xstar) (hN : NetworkHyp Edges B C cl)
    (μi Li : Fin m → ℝ) (h1 : HessBounds K f μi Li)
    (α : ℝ) (hα0 : 0 < α) (hα1 : α ≤ 1)
    (x y xh : ℕ → Fin m → SONATA.Undir.E d) (φ : ℕ → Fin m → ℝ) (hrun : IsRun K f G ft C α x y xh φ) :
    ∀ ν : ℕ,
      sqn (dir x xh ν) ≤
        6 / (μ * phiLb m B cl) *
            ((SONATA.Undir.Dmx Dl Du / SONATA.Undir.mutmn μt + 1) ^ 2 + 4 * SONATA.Undir.Lmx Li ^ 2 / SONATA.Undir.mutmn μt ^ 2) *
            pphi f G xstar (φ ν) (x ν)
          + 3 / SONATA.Undir.mutmn μt ^ 2 * sqn (wperp (φ ν) (y ν)) := by sorry

end SONATA.Push
