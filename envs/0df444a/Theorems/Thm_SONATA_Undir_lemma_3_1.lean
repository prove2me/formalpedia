-- Prove2me | Theorems.Thm_SONATA_Undir_lemma_3_1
-- name    : SONATA.Undir.lemma_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T19:17:49.079341+00:00
-- url     : https://prove2.me/theorems/aa2f3bec-d381-40f2-be3a-d0a322cfe288
-- title:
--   Lemma 3.1, p. 15 — U(xᵢ^{ν+1/2}) ≤ U(xᵢ^ν) − α((1 − α/2)μ̃ᵢ + (α/2)Dᵢˡ)‖dᵢ^ν‖² + α‖dᵢ^ν‖‖δᵢ^ν‖
-- statement:
--   Under the standing assumptions of §3.3, let $(\mathbf x^\nu,\mathbf y^\nu,\hat{\mathbf x}^\nu)$ be a run of SONATA with step size $\alpha\in(0,1]$, $\mathbf d_i^\nu=\hat{\mathbf x}_i^\nu-\mathbf x_i^\nu$, $\mathbf x_i^{\nu+1/2}=\mathbf x_i^\nu+\alpha\mathbf d_i^\nu$ and $\boldsymbol\delta_i^\nu=\nabla F(\mathbf x_i^\nu)-\mathbf y_i^\nu$. Then for every iteration $\nu$ and every agent $i$,
--   $$U(\mathbf x_i^{\nu+1/2})\le U(\mathbf x_i^\nu)-\alpha\Big(\Big(1-\frac\alpha2\Big)\tilde\mu_i+\frac\alpha2D_i^\ell\Big)\|\mathbf d_i^\nu\|^2+\alpha\|\mathbf d_i^\nu\|\,\|\boldsymbol\delta_i^\nu\|,$$
--   where $\tilde\mu_i$ is the strong convexity constant of Assumption C(iii) and $D_i^\ell$ the lower constant of (15).
--
--   The local step decreases the objective up to an error driven by the tracking error. Summed over the agents it is the first half of Proposition 3.4.
-- source:
--   Sun, Daneshmand & Scutari, Distributed Optimization Based on Gradient-tracking Revisited, arXiv:1905.02637v2, p. 15, Lemma 3.1, (28); proof pp. 15–16

import Mathlib
import Definitions.Def_SONATA_Undir_Network
import Definitions.Def_SONATA_Undir_Setting

namespace SONATA.Undir

theorem lemma_3_1
    {m d : ℕ} {K O : Set (E d)} {f : Fin m → E d → ℝ} {G : E d → ℝ} {μ L : ℝ}
    {ft : Fin m → E d → E d → ℝ} {μt Lt Dl Du : Fin m → ℝ} {Gr : SimpleGraph (Fin m)}
    {W : Matrix (Fin m) (Fin m) ℝ} {xstar : E d}
    (hS : Standing K O f G μ L ft μt Lt Dl Du Gr W xstar)
    {α : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1) {x y xh : ℕ → Stack m d}
    (hrun : IsRun K f G ft W α x y xh) :
    ∀ ν i, Uobj f G (xhalf α x xh ν i) ≤
      Uobj f G (x ν i) - α * ((1 - α / 2) * μt i + α / 2 * Dl i) * ‖dir x xh ν i‖ ^ 2
        + α * ‖dir x xh ν i‖ * ‖delta f x y ν i‖ := by sorry

end SONATA.Undir
