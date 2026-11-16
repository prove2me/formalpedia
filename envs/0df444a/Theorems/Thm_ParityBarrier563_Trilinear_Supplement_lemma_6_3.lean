-- Prove2me | Theorems.Thm_ParityBarrier563_Trilinear_Supplement_lemma_6_3
-- name    : ParityBarrier563.Trilinear.Supplement.lemma_6_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T19:46:21.080765+00:00
-- url     : https://prove2.me/theorems/5d3ea02a-82f4-4a81-85c3-20e88d59e1a1
-- title:
--   Lemma 6.3 — Cofactor argument removes the bottom fan-in bound
-- statement:
--   Let $N\ge0$, integers $d,s\ge1$, $0\le R\le N$, a test $\psi:\{0,1\}^N\to[-1,1]$, real $k\ge2\log_2(4s)$ and $\gamma\ge0$ be given. Suppose that for every restriction τ fixing at most R coordinates and every layered depth-d circuit C of size at most s whose restricted bottom fan-in is at most k, $|\mathbb E[\psi_\tau C_\tau]|\le\gamma$. Then every layered depth-d circuit C of size at most s satisfies
--   $$|\mathbb E[\psi C]|\le2\gamma+2^{-R/2}.$$
--   Restricted fan-in counts only live literals. This removes the bottom fan-in bound using hypotheses on every allowed cofactor.
--
--   Differences from the source:
--   - encoding: layered circuits and their restricted bottom fan-in → a layering of the published DAG with a live-literal wire count; reason: constants and fixed literals are omitted from fan-in while every actual gate is counted
--   - encoding: alternating layered circuits, with actual gate count and the stated fan-in bounds → Layering data over the published Circuit DAG, retaining constants and unary gates and counting literal or gate wires; reason: this is the source layer convention and keeps both output types; duplicate wires can be deleted without increasing any bound
-- source:
--   Nikolai Chukhin, Xin Li, Ivan Mihajlin, Yan Zhong, Breaking the Parity Barrier for Constant-Depth Circuits, STOC 2027 submission #563 (October 2026), Lemma 6.3, printed p.27 / PDF p.29

import Definitions.Def_ParityBarrier563_Trilinear_Supplement_Layering

set_option autoImplicit false
open scoped Classical

namespace ParityBarrier563.Trilinear.Supplement

/-- Lemma 6.3: every cofactor of at most R fixed bits, and real fan-in bounds k. -/
theorem lemma_6_3 (N d s R : ℕ) (hd : 1 ≤ d) (hs : 1 ≤ s) (hR : R ≤ N)
    (ψ : RealFn (Fin N)) (hψ : BoundedTest ψ) (k γ : ℝ)
    (hk : 2*Real.logb 2 (4*s) ≤ k) (hγ : 0 ≤ γ)
    (hcofactor : ∀ (τ : Restriction (Fin N)), fixedCount τ ≤ R →
      ∀ (C : Circuit (Fin N)) (L : Layering C d), C.size ≤ s → BottomBound L τ k →
        |avg (fun z => restrict τ ψ z * ind (restrict τ C.eval) z)| ≤ γ) :
  ∀ (C : Circuit (Fin N)) (L : Layering C d), C.size ≤ s →
    |avg (fun x => ψ x * ind C.eval x)| ≤ 2*γ + (2 : ℝ)^(-(R : ℝ)/2) := by sorry

end ParityBarrier563.Trilinear.Supplement
