-- Prove2me | Theorems.Thm_ParityBarrier563_Trilinear_Supplement_theorem_6_4
-- name    : ParityBarrier563.Trilinear.Supplement.theorem_6_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T19:52:13.307287+00:00
-- url     : https://prove2.me/theorems/56d0b61c-e9cd-4017-b641-c9b049e6bbf2
-- title:
--   Theorem 6.4 — Average-case trilinear lower bound with uniform seed and full range
-- statement:
--   Fix an integer $d\ge3$ and $0<\varepsilon<1/(d-1)$. There exist $c_{d,\varepsilon}>0$ and $N_{d,\varepsilon}\ge2$ such that for every $n\ge N_{d,\varepsilon}$, $n\le s\le2^{n^{1/(d-1)-\varepsilon}}$ and every circuit C of depth at most d and size at most s on all $4n-1$ trilinear inputs,
--   $$\left|\Pr_{x,y,a}[C(x,y,a)=f_n(x,y,a)]-\tfrac12\right|\le2^{-c_{d,\varepsilon}n\log_2\log_2 s/(\log_2 s)^{d-1}}.$$
--   All three input blocks are jointly uniform and independent, and both signs of deviation are bounded. Constants depend only on d,ε, before n,s,C. This is the average-case trilinear companion theorem.
--
--   Differences from the source:
--   - encoding: asymptotic agreement bound and sufficiently large n → positive constants and a threshold before n, s and circuit; reason: this spells out the source bound at full strength, with exactly its allowed dependence
--   - encoding: the complete input cube and depth-d AND/OR circuits → the published coordinate types and Circuit, with depth at most d; agreement is a finite uniform probability where used; reason: all blocks remain in the cube, fan-in and fan-out are unrestricted, and size is the number of gates
-- source:
--   Nikolai Chukhin, Xin Li, Ivan Mihajlin, Yan Zhong, Breaking the Parity Barrier for Constant-Depth Circuits, STOC 2027 submission #563 (October 2026), Theorem 6.4, printed p.28 / PDF p.30

import Definitions.Def_ParityBarrier563_Trilinear_Supplement_FiniteAverages
import Definitions.Def_ParityBarrier563_Trilinear_Circuit
import Definitions.Def_ParityBarrier563_Trilinear_TrilinearFunction

set_option autoImplicit false
open scoped Classical

namespace ParityBarrier563.Trilinear.Supplement

/-- Theorem 6.4: uniform agreement on all input blocks and the entire printed size range. -/
theorem theorem_6_4 (d : ℕ) (hd : 3 ≤ d) (ε : ℝ)
    (hε : 0 < ε) (hε1 : ε < 1/((d : ℝ)-1)) :
  ∃ (c : ℝ) (N : ℕ), 0 < c ∧ 2 ≤ N ∧ ∀ n : ℕ, N ≤ n →
    ∀ s : ℝ, (n : ℝ) ≤ s → s ≤ (2 : ℝ)^((n : ℝ)^(1/((d : ℝ)-1)-ε)) →
    ∀ C : Circuit (TriVar n), C.depth ≤ d → (C.size : ℝ) ≤ s →
      |agreement C.eval (trilinearFn n) - 1/2| ≤ (2 : ℝ)^(-c*averageExponent d n s) := by sorry

end ParityBarrier563.Trilinear.Supplement
