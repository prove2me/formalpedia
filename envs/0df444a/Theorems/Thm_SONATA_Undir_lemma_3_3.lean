-- Prove2me | Theorems.Thm_SONATA_Undir_lemma_3_3
-- name    : SONATA.Undir.lemma_3_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T19:17:21.114339+00:00
-- url     : https://prove2.me/theorems/ee6ffd19-45f9-48c1-a9a8-d773860a947b
-- title:
--   Lemma 3.3, p. 17 — ‖δ^ν‖² ≤ 4L²_mx‖x_⊥^ν‖² + 2‖y_⊥^ν‖²
-- statement:
--   Under the standing assumptions of §3.3, let $L_i$ be constants as in (1), $0<L_i<\infty$ with $\mu_i\mathbf I\preceq\nabla^2f_i(\mathbf x)\preceq L_i\mathbf I$ on $\mathcal K$ for some $\mu_i\ge0$, and $L_{\rm mx}=\max_iL_i$. For every run of SONATA with step size $\alpha\in(0,1]$ and every $\nu$,
--   $$\|\boldsymbol\delta^\nu\|^2\le4L_{\rm mx}^2\|\mathbf x_\perp^\nu\|^2+2\|\mathbf y_\perp^\nu\|^2,$$
--   where $\boldsymbol\delta^\nu$ stacks $\boldsymbol\delta_i^\nu=\nabla F(\mathbf x_i^\nu)-\mathbf y_i^\nu$ and $\mathbf x_\perp^\nu$, $\mathbf y_\perp^\nu$ are the consensus errors (22).
--
--   The tracking error is controlled by the two consensus errors; this is how consensus enters the descent estimate of Proposition 3.4.
-- source:
--   Sun, Daneshmand & Scutari, Distributed Optimization Based on Gradient-tracking Revisited, arXiv:1905.02637v2, p. 17, Lemma 3.3, (39); proof p. 18

import Mathlib
import Definitions.Def_SONATA_Undir_Network
import Definitions.Def_SONATA_Undir_Setting

namespace SONATA.Undir

theorem lemma_3_3
    {m d : ℕ} {K O : Set (E d)} {f : Fin m → E d → ℝ} {G : E d → ℝ} {μ L : ℝ}
    {ft : Fin m → E d → E d → ℝ} {μt Lt Dl Du : Fin m → ℝ} {Gr : SimpleGraph (Fin m)}
    {W : Matrix (Fin m) (Fin m) ℝ} {xstar : E d}
    (hS : Standing K O f G μ L ft μt Lt Dl Du Gr W xstar)
    {μi Li : Fin m → ℝ} (h1 : Eq1 K f μi Li)
    {α : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1) {x y xh : ℕ → Stack m d}
    (hrun : IsRun K f G ft W α x y xh) :
    ∀ ν, stackNormSq (delta f x y ν) ≤
      4 * Lmx Li ^ 2 * stackNormSq (perp (x ν)) + 2 * stackNormSq (perp (y ν)) := by sorry

end SONATA.Undir
