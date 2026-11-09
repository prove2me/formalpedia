-- Prove2me | Theorems.Thm_ParityBarrier563_Trilinear_theorem_1_1
-- name    : ParityBarrier563.Trilinear.theorem_1_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:10:35.421171+00:00
-- url     : https://prove2.me/theorems/ffc71707-e82a-4b8a-9b9e-08f99f0c3c5a
-- title:
--   Theorem 1.1 — every depth-d circuit computing the trilinear function f_n has 2^{Ω((n log n)^{1/(d−1)})} gates
-- statement:
--   Let $f_n(x,y,a)=\sum_{i=0}^{n-1}\sum_{j=0}^{n-1}a_{i+j}x_iy_j \bmod 2$ for $x,y\in\{0,1\}^n$ and $a\in\{0,1\}^{2n-1}$. For every fixed integer $d\ge3$ there are a constant $c=c(d)>0$ and a threshold $N=N(d)\ge2$ such that for every $n\ge N$, every circuit of AND and OR gates of unbounded fan-in and fan-out, reading literals and constants, of depth at most $d$, that computes $f_n$ on its $4n-1$ input bits has
--
--   $$\mathrm{size}\ \ge\ 2^{\,c\,(n\log_2 n)^{1/(d-1)}}$$
--
--   gates. The circuit need not be layered, and its output gate may be of either type.
--
--   This is the paper's headline result: an explicit function in P whose depth-$d$ complexity exceeds the parity barrier $2^{\Theta(n^{1/(d-1)})}$ at every constant depth.
--
--   Differences from the source:
--   - encoding: has 2^{Ω((n log n)^{1/(d−1)})} gates → ∃ c > 0 and N ≥ 2, depending only on d, such that every such circuit for f_n with n ≥ N has size ≥ 2^{c·(n·log₂ n)^{1/(d−1)}}; reason: the meaning of the Ω-notation; logarithms are base two (§2); the exponent 1/(d−1) is a real power
--   - generalization: depth-d circuits of AND/OR gates reading literals and constants, with the output an AND or OR gate → circuits whose output may be any node (a gate, a literal or a constant) and whose gates may have fan-in zero; reason: these only add circuits: every circuit of the source is one of them with the same size and depth, so the Lean statement specializes to the source's
-- source:
--   Nikolai Chukhin, Xin Li, Ivan Mihajlin, Yan Zhong, Breaking the Parity Barrier for Constant-Depth Circuits, STOC 2027 submission #563 (October 2026), SHA-256 e50e7ff9480ef7c23095e91345faf20f73773bc111e3b0eed2da71a28f7f9462, Theorem 1.1, printed p.2 (PDF p.4); proof printed p.19 (PDF p.21)

import Mathlib
import Definitions.Def_ParityBarrier563_Trilinear_Circuit
import Definitions.Def_ParityBarrier563_Trilinear_TrilinearFunction

set_option autoImplicit false

namespace ParityBarrier563.Trilinear

/-- Theorem 1.1, printed p.2 / PDF 4: for every fixed `d ≥ 3`, every circuit of depth at most
`d` computing `f_n` has `2^{Ω((n log₂ n)^{1/(d−1)})}` gates. -/
theorem theorem_1_1 (d : ℕ) (hd : 3 ≤ d) :
    ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, 2 ≤ N ∧ ∀ n : ℕ, N ≤ n →
      ∀ C : Circuit (TriVar n), C.depth ≤ d → C.Computes (trilinearFn n) →
        (2 : ℝ) ^ (c * ((n : ℝ) * Real.logb 2 n) ^ (1 / ((d : ℝ) - 1))) ≤ C.size := by sorry

end ParityBarrier563.Trilinear
