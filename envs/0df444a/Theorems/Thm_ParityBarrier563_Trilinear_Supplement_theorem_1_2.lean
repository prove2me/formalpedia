-- Prove2me | Theorems.Thm_ParityBarrier563_Trilinear_Supplement_theorem_1_2
-- name    : ParityBarrier563.Trilinear.Supplement.theorem_1_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T19:44:14.746929+00:00
-- url     : https://prove2.me/theorems/8d59030b-2761-4764-ad9a-41bd35f75956
-- title:
--   Theorem 1.2 — Worst-case inverse-trace lower bound at every constant depth
-- statement:
--   For every fixed integer $d\ge3$ there exist $c_d>0$ and $N_d\ge2$ such that for all $n\ge N_d$, every basis e of $\mathbb F_{2^n}$ and every AND/OR circuit C of depth at most d computing inverse trace in that basis,
--   $$\operatorname{size}(C)\ge2^{c_d(n\log_2 n)^{1/(d-1)}}.$$
--   Size counts gates, fan-in and fan-out are unrestricted, and either output gate is allowed. Constants depend only on d. This extends the worst-case lower bound to the seedless inverse-trace function.
--
--   Differences from the source:
--   - encoding: asymptotic gate bound and sufficiently large n → positive constants and a threshold before n, basis and circuit; reason: this spells out the source bound at full strength, with exactly its allowed dependence
--   - encoding: the field of order 2^n in every binary basis → an arbitrary field K with an F₂-algebra structure and an n-vector basis; reason: the basis bijects K with F₂^n and enforces order 2^n without any additional restriction
-- source:
--   Nikolai Chukhin, Xin Li, Ivan Mihajlin, Yan Zhong, Breaking the Parity Barrier for Constant-Depth Circuits, STOC 2027 submission #563 (October 2026), Theorem 1.2, printed p.3 / PDF p.5

import Definitions.Def_ParityBarrier563_Trilinear_Supplement_InverseTrace
import Definitions.Def_ParityBarrier563_Trilinear_Circuit

set_option autoImplicit false
open scoped Classical

namespace ParityBarrier563.Trilinear.Supplement

/-- Theorem 1.2: every basis, both output types, arbitrary DAG circuits, all fixed d≥3. -/
theorem theorem_1_2 (d : ℕ) (hd : 3 ≤ d) :
  ∃ (c : ℝ) (N : ℕ), 0 < c ∧ 2 ≤ N ∧ ∀ n : ℕ, N ≤ n →
    ∀ (K : Type) [Field K] [Algebra (ZMod 2) K]
      (e : Module.Basis (Fin n) (ZMod 2) K) (C : Circuit (Fin n)),
    C.depth ≤ d → C.Computes (inverseTrace e) →
    (2 : ℝ)^(c*((n : ℝ)*Real.logb 2 n)^(1/((d : ℝ)-1))) ≤ C.size := by sorry

end ParityBarrier563.Trilinear.Supplement
