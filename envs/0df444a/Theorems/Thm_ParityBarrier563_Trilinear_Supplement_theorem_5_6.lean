-- Prove2me | Theorems.Thm_ParityBarrier563_Trilinear_Supplement_theorem_5_6
-- name    : ParityBarrier563.Trilinear.Supplement.theorem_5_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T19:50:25.801365+00:00
-- url     : https://prove2.me/theorems/380f29a8-6299-4819-a97c-0ad4130be0b5
-- title:
--   Theorem 5.6 — Hashed polynomial evaluation: lower bound for every constant depth
-- statement:
--   For every fixed integer $d\ge3$ there exist $c_d>0$ and $N_d\ge64$ such that for every $n\ge N_d$ and every input length $5n,\ldots,5n+4$, every depth-at-most-d circuit C computing the entire padded hashed polynomial evaluation function satisfies
--   $$\operatorname{size}(C)\ge2^{c_d(n\log_2 n)^{1/(d-1)}}.$$
--   The hash, every monic modulus P of degree $\lceil n^{2/3}\rceil$ and all polynomial coefficients are input bits; trailing bits are ignored. Constants depend only on d and are uniform in the padding. This covers the full evaluator, beyond any selected hard slice.
--
--   Differences from the source:
--   - encoding: asymptotic gate bound and sufficiently large n → positive constants and a threshold before n, padding and circuit; reason: this spells out the source bound at full strength, with exactly its allowed dependence
--   - encoding: the complete input cube and depth-d AND/OR circuits → the published coordinate types and Circuit, with depth at most d; agreement is a finite uniform probability where used; reason: all blocks remain in the cube, fan-in and fan-out are unrestricted, and size is the number of gates
-- source:
--   Nikolai Chukhin, Xin Li, Ivan Mihajlin, Yan Zhong, Breaking the Parity Barrier for Constant-Depth Circuits, STOC 2027 submission #563 (October 2026), Theorem 5.6, printed p.20 / PDF p.22

import Definitions.Def_ParityBarrier563_Trilinear_Supplement_HashedEvaluation
import Definitions.Def_ParityBarrier563_Trilinear_Circuit

set_option autoImplicit false
open scoped Classical

namespace ParityBarrier563.Trilinear.Supplement

/-- Theorem 5.6, every padded input length and all monic input moduli. -/
theorem theorem_5_6 (d : ℕ) (hd : 3 ≤ d) :
  ∃ (c : ℝ) (N : ℕ), 0 < c ∧ 64 ≤ N ∧ ∀ n : ℕ, N ≤ n →
    ∀ (padding : Fin 5) (C : Circuit (Fin (5*n+padding.val))),
    C.depth ≤ d → C.Computes (hashedFn n padding) →
      (2 : ℝ)^(c*((n : ℝ)*Real.logb 2 n)^(1/((d : ℝ)-1))) ≤ C.size := by sorry

end ParityBarrier563.Trilinear.Supplement
