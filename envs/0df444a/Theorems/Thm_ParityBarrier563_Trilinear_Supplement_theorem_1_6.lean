-- Prove2me | Theorems.Thm_ParityBarrier563_Trilinear_Supplement_theorem_1_6
-- name    : ParityBarrier563.Trilinear.Supplement.theorem_1_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T19:49:23.129135+00:00
-- url     : https://prove2.me/theorems/f2f5cf45-78bd-49f8-83f3-8a628c73d6ff
-- title:
--   Theorem 1.6 — Trilinear upper bound at every constant depth
-- statement:
--   For every fixed integer $d\ge3$ there exist $A_d>0$ and $N_d\ge1$ such that for every $n\ge N_d$ the complete trilinear function $f_n(x,y,a)=\sum_{i,j<n}a_{i+j}x_iy_j\pmod2$ has an AND/OR circuit C with
--   $$\operatorname{depth}(C)\le d,\quad C=f_n,\quad\operatorname{size}(C)\le2^{A_dn^{2/d}}.$$
--   The circuit reads all $4n-1$ input coordinates, including the seed block. Constants depend only on d. This companion upper bound complements the published goal's lower bound.
--
--   Differences from the source:
--   - encoding: asymptotic circuit-existence upper bound → positive A_d and a threshold before n and the existential circuit; reason: this spells out the source bound at full strength, with exactly its allowed dependence
--   - encoding: the complete input cube and depth-d AND/OR circuits → the published coordinate types and Circuit, with depth at most d; agreement is a finite uniform probability where used; reason: all blocks remain in the cube, fan-in and fan-out are unrestricted, and size is the number of gates
-- source:
--   Nikolai Chukhin, Xin Li, Ivan Mihajlin, Yan Zhong, Breaking the Parity Barrier for Constant-Depth Circuits, STOC 2027 submission #563 (October 2026), Theorem 1.6, printed p.4 / PDF p.6

import Definitions.Def_ParityBarrier563_Trilinear_Supplement_FiniteAverages
import Definitions.Def_ParityBarrier563_Trilinear_Circuit
import Definitions.Def_ParityBarrier563_Trilinear_TrilinearFunction

set_option autoImplicit false
open scoped Classical

namespace ParityBarrier563.Trilinear.Supplement

/-- Theorem 1.6: existence on the whole trilinear cube, including its seed block. -/
theorem theorem_1_6 (d : ℕ) (hd : 3 ≤ d) :
  ∃ (A : ℝ) (N : ℕ), 0 < A ∧ 1 ≤ N ∧ ∀ n : ℕ, N ≤ n →
    ∃ C : Circuit (TriVar n), C.depth ≤ d ∧ C.Computes (trilinearFn n) ∧
      (C.size : ℝ) ≤ (2 : ℝ)^(A*(n : ℝ)^(2/(d : ℝ))) := by sorry

end ParityBarrier563.Trilinear.Supplement
