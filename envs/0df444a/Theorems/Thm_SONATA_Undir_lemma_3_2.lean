-- Prove2me | Theorems.Thm_SONATA_Undir_lemma_3_2
-- name    : SONATA.Undir.lemma_3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T19:17:42.218873+00:00
-- url     : https://prove2.me/theorems/6d554942-988a-48bf-a5cd-b776fda72ee1
-- title:
--   Lemma 3.2, p. 16 — α‖d^ν‖² ≥ (μ/D²_mx)(p^{ν+1} − (1 − α)p^ν − (α/μ)‖δ^ν‖²)
-- statement:
--   Under the standing assumptions of §3.3, let $(\mathbf x^\nu,\mathbf y^\nu,\hat{\mathbf x}^\nu)$ be a run of SONATA with step size $\alpha\in(0,1]$, with stacked direction $\mathbf d^\nu$, stacked tracking error $\boldsymbol\delta^\nu$ and optimality gap $p^\nu=\sum_i(U(\mathbf x_i^\nu)-U(\mathbf x^\star))$. Then for every $\nu$,
--   $$\alpha\|\mathbf d^\nu\|^2\ge\frac{\mu}{D_{\rm mx}^2}\Big(p^{\nu+1}-(1-\alpha)p^\nu-\frac\alpha\mu\|\boldsymbol\delta^\nu\|^2\Big),$$
--   where $D_{\rm mx}=\max_i\max\{|D_i^\ell|,|D_i^u|\}$ from (15), (24), and the norms are Euclidean norms of stacked vectors, $\|\mathbf d^\nu\|^2=\sum_i\|\mathbf d_i^\nu\|^2$.
--
--   The step length bounds the progress of the optimality gap from below; together with Lemma 3.1 it gives Proposition 3.4.
--
--   **Formalization Note.** When $D_{\rm mx}=0$ the page divides by zero; in Lean $\mu/0=0$ and the inequality reads $\alpha\|\mathbf d^\nu\|^2\ge0$. No hypothesis $D_{\rm mx}>0$ is added.
-- source:
--   Sun, Daneshmand & Scutari, Distributed Optimization Based on Gradient-tracking Revisited, arXiv:1905.02637v2, p. 16, Lemma 3.2, (35); proof p. 17

import Mathlib
import Definitions.Def_SONATA_Undir_Network
import Definitions.Def_SONATA_Undir_Setting

namespace SONATA.Undir

theorem lemma_3_2
    {m d : ℕ} {K O : Set (E d)} {f : Fin m → E d → ℝ} {G : E d → ℝ} {μ L : ℝ}
    {ft : Fin m → E d → E d → ℝ} {μt Lt Dl Du : Fin m → ℝ} {Gr : SimpleGraph (Fin m)}
    {W : Matrix (Fin m) (Fin m) ℝ} {xstar : E d}
    (hS : Standing K O f G μ L ft μt Lt Dl Du Gr W xstar)
    {α : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1) {x y xh : ℕ → Stack m d}
    (hrun : IsRun K f G ft W α x y xh) :
    ∀ ν, α * stackNormSq (dir x xh ν) ≥
      μ / Dmx Dl Du ^ 2 * (pgap f G xstar x (ν + 1) - (1 - α) * pgap f G xstar x ν
        - α / μ * stackNormSq (delta f x y ν)) := by sorry

end SONATA.Undir
