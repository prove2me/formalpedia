-- Prove2me | Theorems.Thm_SONATA_Push_lemma_I_3
-- name    : SONATA.Push.lemma_I_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T20:14:04.311686+00:00
-- url     : https://prove2.me/theorems/5f0c2bd6-8e0b-48f2-91c8-93f4c01b150b
-- title:
--   Lemma I.3, p. 48 — ‖δ‖² ≤ 8L²_mx‖x_{φ,⊥}‖² + 2‖y_{φ,⊥}‖²
-- statement:
--   In the standing setting (Assumptions A, B′, C, E, the constants (15), a solution $x^\star$), let the constants $\mu_i\ge0$, $L_i>0$ satisfy (1) and $L_{\rm mx}=\max_iL_i$. For every run of Algorithm 3 with step size $\alpha\in(0,1]$ and every $\nu$, the tracking error satisfies
--   $$\|\delta^\nu\|^2\le8L_{\rm mx}^2\|x^\nu_{\phi,\perp}\|^2+2\|y^\nu_{\phi,\perp}\|^2,$$
--   where $\|\delta^\nu\|^2=\sum_i\|\nabla F(x_i^\nu)-y_i^\nu\|^2$ and the consensus errors are measured against the $\phi$-weighted averages (75)–(76).
--
--   The tracking error is controlled by the two consensus errors, which is what lets the network part of the analysis feed into the optimization part.
-- source:
--   Sun, Daneshmand & Scutari, Distributed Optimization Based on Gradient-tracking Revisited, arXiv:1905.02637v2, p. 48, Supporting Material, Lemma I.3, (13); L_mx from (4), p. 7 and (1)

import Mathlib
import Definitions.Def_SONATA_Push_Network

namespace SONATA.Push

/-- Lemma I.3 (Supporting Material, (13), p. 48): the tracking error satisfies
`‖δ^ν‖² ≤ 8 L²_mx ‖x_{φ,⊥}^ν‖² + 2 ‖y_{φ,⊥}^ν‖²`, with `L_mx = max_i L_i` from (1). -/
theorem lemma_I_3
    {m d : ℕ} (K O : Set (SONATA.Undir.E d)) (f : Fin m → SONATA.Undir.E d → ℝ) (G : SONATA.Undir.E d → ℝ) (μ L : ℝ)
    (ft : Fin m → SONATA.Undir.E d → SONATA.Undir.E d → ℝ) (μt Lt Dl Du : Fin m → ℝ) (xstar : SONATA.Undir.E d)
    (Edges : ℕ → Fin m → Fin m → Prop) (B : ℕ) (C : ℕ → Matrix (Fin m) (Fin m) ℝ) (cl : ℝ)
    (hP : ProblemHyp K O f G μ L ft μt Lt Dl Du xstar) (hN : NetworkHyp Edges B C cl)
    (μi Li : Fin m → ℝ) (h1 : HessBounds K f μi Li)
    (α : ℝ) (hα0 : 0 < α) (hα1 : α ≤ 1)
    (x y xh : ℕ → Fin m → SONATA.Undir.E d) (φ : ℕ → Fin m → ℝ) (hrun : IsRun K f G ft C α x y xh φ) :
    ∀ ν : ℕ,
      sqn (delta f (x ν) (y ν)) ≤
        8 * SONATA.Undir.Lmx Li ^ 2 * sqn (wperp (φ ν) (x ν)) + 2 * sqn (wperp (φ ν) (y ν)) := by sorry

end SONATA.Push
