-- Prove2me | Theorems.Thm_ParityBarrier563_Trilinear_Supplement_theorem_1_5
-- name    : ParityBarrier563.Trilinear.Supplement.theorem_1_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T19:48:40.834198+00:00
-- url     : https://prove2.me/theorems/37c1b31a-92e9-4bb9-8db2-04bcce0461d6
-- title:
--   Theorem 1.5 — Inverse trace: polynomial top fan-in forces exponential size
-- statement:
--   For every real $A>0$ there exist $c_A>0$ and $N_A\ge2$ such that for every $n\ge N_A$, every basis of $\mathbb F_{2^n}$ and every alternating layered depth-three circuit C of top fan-in at most $n^A$ computing inverse trace,
--   $$\operatorname{size}(C)>2^{c_A n}.$$
--   The inequality is strict, either output type is allowed and A is arbitrary. This gives exponential size under any fixed polynomial top fan-in bound.
--
--   Differences from the source:
--   - encoding: asymptotic gate bound and sufficiently large n → positive constants and a threshold before n, basis and circuit; reason: this spells out the source bound at full strength, with exactly its allowed dependence
--   - encoding: the field of order 2^n in every binary basis → an arbitrary field K with an F₂-algebra structure and an n-vector basis; reason: the basis bijects K with F₂^n and enforces order 2^n without any additional restriction
--   - encoding: alternating layered circuits, with actual gate count and the stated fan-in bounds → Layering data over the published Circuit DAG, retaining constants and unary gates and counting literal or gate wires; reason: this is the source layer convention and keeps both output types; duplicate wires can be deleted without increasing any bound
-- source:
--   Nikolai Chukhin, Xin Li, Ivan Mihajlin, Yan Zhong, Breaking the Parity Barrier for Constant-Depth Circuits, STOC 2027 submission #563 (October 2026), Theorem 1.5, printed p.4 / PDF p.6

import Definitions.Def_ParityBarrier563_Trilinear_Supplement_InverseTrace
import Definitions.Def_ParityBarrier563_Trilinear_Supplement_Layering

set_option autoImplicit false
open scoped Classical

namespace ParityBarrier563.Trilinear.Supplement

/-- Theorem 1.5, preserving the strict inequality and arbitrary positive polynomial degree. -/
theorem theorem_1_5 (A : ℝ) (hA : 0 < A) :
  ∃ (c : ℝ) (N : ℕ), 0 < c ∧ 2 ≤ N ∧ ∀ n : ℕ, N ≤ n →
    ∀ (K : Type) [Field K] [Algebra (ZMod 2) K]
      (e : Module.Basis (Fin n) (ZMod 2) K)
      (C : Circuit (Fin n)) (L : Layering C 3),
    TopBound L ((n : ℝ)^A) → C.Computes (inverseTrace e) →
      (2 : ℝ)^(c*n) < C.size := by sorry

end ParityBarrier563.Trilinear.Supplement
