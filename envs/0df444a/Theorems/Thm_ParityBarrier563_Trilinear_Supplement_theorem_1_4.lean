-- Prove2me | Theorems.Thm_ParityBarrier563_Trilinear_Supplement_theorem_1_4
-- name    : ParityBarrier563.Trilinear.Supplement.theorem_1_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T19:48:13.956062+00:00
-- url     : https://prove2.me/theorems/30e5b419-3fbe-4b67-8ec7-54818e21c091
-- title:
--   Theorem 1.4 — Inverse trace: layered depth three with bounded bottom fan-in
-- statement:
--   For every $\varepsilon>0$ there exist $c_\varepsilon>0$ and $N_\varepsilon\ge2$ such that for every $n\ge N_\varepsilon$, every basis of $\mathbb F_{2^n}$ and every real $k\ge(\log_2 n)^{1+\varepsilon}$, every alternating layered depth-three circuit C computing inverse trace with bottom fan-in at most k satisfies
--   $$\operatorname{size}(C)\ge2^{c_\varepsilon n\log_2 k/k}.$$
--   Either output type is permitted and there is no upper bound on k. Constants are uniform in k,n,basis. This is the stronger lower bound for restricted bottom fan-in.
--
--   Differences from the source:
--   - encoding: asymptotic gate bound and sufficiently large n → positive constants and a threshold before n, basis and circuit; reason: this spells out the source bound at full strength, with exactly its allowed dependence
--   - encoding: the field of order 2^n in every binary basis → an arbitrary field K with an F₂-algebra structure and an n-vector basis; reason: the basis bijects K with F₂^n and enforces order 2^n without any additional restriction
--   - encoding: alternating layered circuits, with actual gate count and the stated fan-in bounds → Layering data over the published Circuit DAG, retaining constants and unary gates and counting literal or gate wires; reason: this is the source layer convention and keeps both output types; duplicate wires can be deleted without increasing any bound
-- source:
--   Nikolai Chukhin, Xin Li, Ivan Mihajlin, Yan Zhong, Breaking the Parity Barrier for Constant-Depth Circuits, STOC 2027 submission #563 (October 2026), Theorem 1.4, printed p.4 / PDF p.6

import Definitions.Def_ParityBarrier563_Trilinear_Supplement_InverseTrace
import Definitions.Def_ParityBarrier563_Trilinear_Supplement_Layering

set_option autoImplicit false
open scoped Classical

namespace ParityBarrier563.Trilinear.Supplement

/-- Theorem 1.4, including unbounded real k and both output kinds. -/
theorem theorem_1_4 (ε : ℝ) (hε : 0 < ε) :
  ∃ (c : ℝ) (N : ℕ), 0 < c ∧ 2 ≤ N ∧ ∀ n : ℕ, N ≤ n →
    ∀ (K : Type) [Field K] [Algebra (ZMod 2) K]
      (e : Module.Basis (Fin n) (ZMod 2) K) (k : ℝ),
    (Real.logb 2 n)^(1+ε) ≤ k →
    ∀ (C : Circuit (Fin n)) (L : Layering C 3),
    BottomBoundFull L k → C.Computes (inverseTrace e) →
      (2 : ℝ)^(c*n*Real.logb 2 k/k) ≤ C.size := by sorry

end ParityBarrier563.Trilinear.Supplement
