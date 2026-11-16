-- Prove2me | Theorems.Thm_ParityBarrier563_Trilinear_Supplement_lemma_6_2
-- name    : ParityBarrier563.Trilinear.Supplement.lemma_6_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T19:45:45.545568+00:00
-- url     : https://prove2.me/theorems/6f6cfe37-008f-4f4d-9564-7e0891623385
-- title:
--   Lemma 6.2 — Both depth-two restriction bounds for layered circuits
-- statement:
--   Fix an integer $d\ge3$. There exist functions k(s),q(s), positive comparison constants and $A_d>0$, depending only on d, with $k(s)\ge1$, $0<q(s)\le1$, $k(s)=\Theta_d(\log_2 s)$ and $1/q(s)=\Theta_d((\log_2 s)^{d-2})$ for every integer $s\ge2$. For every finite variable set V, every layered depth-d circuit C of size at most s and bottom fan-in at most $3\log_2(4s)$, every $\psi:\{0,1\}^V\to[-1,1]$ and integer $D\ge1$, let $E=\mathbb E_\varphi\operatorname{corr}_{k(s)}(\psi_\varphi)$ for a q(s)-random restriction. Both estimates hold:
--   $$|\mathbb E[\psi C]|\le d s^{-3}+2E,\qquad |\mathbb E[\psi C]|\le s^{A_d}2^{-D}+2^{2^{d-2}D}E.$$
--   The same k,q work before choosing V,C,ψ,D. This is the depth-two reduction needed for average-case bounds.
--
--   Differences from the source:
--   - encoding: Θ_d parameters and O_d exponent → positive comparison constants, functions k(s),q(s), and A before s,V,C,ψ,D; reason: this spells out the source uniformity and both estimates for one choice of parameters
--   - encoding: alternating layered circuits, with actual gate count and the stated fan-in bounds → Layering data over the published Circuit DAG, retaining constants and unary gates and counting literal or gate wires; reason: this is the source layer convention and keeps both output types; duplicate wires can be deleted without increasing any bound
-- source:
--   Nikolai Chukhin, Xin Li, Ivan Mihajlin, Yan Zhong, Breaking the Parity Barrier for Constant-Depth Circuits, STOC 2027 submission #563 (October 2026), Lemma 6.2, printed p.26 / PDF p.28

import Definitions.Def_ParityBarrier563_Trilinear_Supplement_Layering
import Definitions.Def_ParityBarrier563_Trilinear_Correlation

set_option autoImplicit false
open scoped Classical

namespace ParityBarrier563.Trilinear.Supplement

/-- Lemma 6.2: one choice of k(s),q(s) works for both estimates and every test and D. -/
theorem lemma_6_2 (d : ℕ) (hd : 3 ≤ d) :
  ∃ (ak bk aq bq A : ℝ) (k : ℕ → ℕ) (q : ℕ → ℝ),
    0 < ak ∧ 0 < bk ∧ 0 < aq ∧ 0 < bq ∧ 0 < A ∧
    ∀ s : ℕ, 2 ≤ s →
      1 ≤ k s ∧ 0 < q s ∧ q s ≤ 1 ∧
      ak*Real.logb 2 s ≤ k s ∧ (k s : ℝ) ≤ bk*Real.logb 2 s ∧
      aq*(Real.logb 2 s)^(d-2) ≤ 1/q s ∧
      1/q s ≤ bq*(Real.logb 2 s)^(d-2) ∧
      ∀ (V : Type) [Fintype V] [DecidableEq V] (C : Circuit V) (L : Layering C d),
        C.size ≤ s → BottomBoundFull L (3*Real.logb 2 (4*s)) →
      ∀ (ψ : RealFn V), BoundedTest ψ → ∀ D : ℕ, 1 ≤ D →
        let E := restrExpect (q s) (fun φ => corr (k s) (restrict φ ψ))
        |avg (fun x => ψ x * ind C.eval x)| ≤ (d : ℝ)/(s : ℝ)^3 + 2*E ∧
        |avg (fun x => ψ x * ind C.eval x)| ≤
          (s : ℝ)^A * (2 : ℝ)^(-(D : ℝ)) +
          (2 : ℝ)^((2 : ℕ)^(d-2)*D) * E := by sorry

end ParityBarrier563.Trilinear.Supplement
