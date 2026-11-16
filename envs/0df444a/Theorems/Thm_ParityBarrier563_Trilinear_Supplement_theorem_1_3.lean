-- Prove2me | Theorems.Thm_ParityBarrier563_Trilinear_Supplement_theorem_1_3
-- name    : ParityBarrier563.Trilinear.Supplement.theorem_1_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T19:47:37.873207+00:00
-- url     : https://prove2.me/theorems/88429b16-0728-43cd-b168-35eb088d5c25
-- title:
--   Theorem 1.3 — Uniform average-case inverse-trace bound with its full size range
-- statement:
--   For every integer $d\ge3$ there exist $a_d,c_d>0$ and $N_d\ge2$ such that for every $n\ge N_d$, every basis e of $\mathbb F_{2^n}$ and every $n\le s\le2^{a_dn^{1/(d-1)}}$, every circuit C of depth at most d and size at most s satisfies
--   $$\left|\Pr_x[C(x)=I_e(x)]-\tfrac12\right|\le2^{-c_d n\log_2\log_2 s/(\log_2 s)^{d-1}}.$$
--   The input x is uniform on the full Boolean cube. Both signs of the advantage are bounded, arbitrary base-model circuits are included, and constants depend only on d. This is the average-case inverse-trace companion theorem.
--
--   Differences from the source:
--   - encoding: asymptotic agreement bound and sufficiently large n → positive size-range and correlation constants and a threshold before n, field, basis, s and circuit; reason: this spells out the source bound at full strength, with exactly its allowed dependence
--   - encoding: the field of order 2^n in every binary basis → an arbitrary field K with an F₂-algebra structure and an n-vector basis; reason: the basis bijects K with F₂^n and enforces order 2^n without any additional restriction
--   - encoding: the complete input cube and depth-d AND/OR circuits → the published coordinate types and Circuit, with depth at most d; agreement is a finite uniform probability where used; reason: all blocks remain in the cube, fan-in and fan-out are unrestricted, and size is the number of gates
-- source:
--   Nikolai Chukhin, Xin Li, Ivan Mihajlin, Yan Zhong, Breaking the Parity Barrier for Constant-Depth Circuits, STOC 2027 submission #563 (October 2026), Theorem 1.3, printed p.3 / PDF p.5

import Definitions.Def_ParityBarrier563_Trilinear_Supplement_InverseTrace
import Definitions.Def_ParityBarrier563_Trilinear_Circuit

set_option autoImplicit false
open scoped Classical

namespace ParityBarrier563.Trilinear.Supplement

/-- Theorem 1.3: arbitrary base-model circuits and absolute deviation from one half. -/
theorem theorem_1_3 (d : ℕ) (hd : 3 ≤ d) :
  ∃ (a c : ℝ) (N : ℕ), 0 < a ∧ 0 < c ∧ 2 ≤ N ∧ ∀ n : ℕ, N ≤ n →
    ∀ (K : Type) [Field K] [Algebra (ZMod 2) K]
      (e : Module.Basis (Fin n) (ZMod 2) K) (s : ℝ),
    (n : ℝ) ≤ s → s ≤ (2 : ℝ)^(a*(n : ℝ)^(1/((d : ℝ)-1))) →
    ∀ C : Circuit (Fin n), C.depth ≤ d → (C.size : ℝ) ≤ s →
      |agreement C.eval (inverseTrace e) - 1/2| ≤ (2 : ℝ)^(-c*averageExponent d n s) := by sorry

end ParityBarrier563.Trilinear.Supplement
