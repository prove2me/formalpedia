-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P07_lossless_memory
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P07.lossless_memory
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T04:36:35.294983+00:00
-- url     : https://prove2.me/theorems/fcd8e2b4-fc53-45f6-b39d-705f87b3bf92
-- title:
--   §1.2: exact lossless memory
-- statement:
--   Let $p$ be a probability law on a finite nonempty alphabet $X$. A code consists of an encoder into an alphabet of $m\ge1$ symbols and a decoder, and its error is the probability of recovering the wrong source symbol. Logs are binary, and $H(p)$ is Shannon entropy. Introductory smooth max-entropy minimizes the order-$1/2$ Rényi entropy over normalized probability laws within variational distance $\varepsilon$.
--
--   The minimum fixed binary memory for zero-error source compression is ceil(log2 |supp ρ_X|).
--
--   $$
--   m_{\rm bits}^{\rm exact}=\left\lceil\log_2|\operatorname{supp}p|\right\rceil.
--   $$
--
--   This result records the source’s operational or structural relation, with the stated endpoint and attainment clauses retained.
-- source:
--   Quantum Information Processing with Finite Resources -- Mathematical Foundations, arXiv:1504.00233v5, PDF p. 12, §1.2: exact lossless memory

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P07

noncomputable section

open Filter

open scoped BigOperators Matrix ComplexConjugate ComplexOrder Matrix.Norms.L2Operator Topology

namespace QAlgorithms.Papers.Independent.Intakenext100.P07

attribute [local instance] Classical.propDecidable Classical.decEq

variable {I J A B C D X Y Z : Type*}

variable [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

variable [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

variable [Fintype C] [DecidableEq C] [Fintype D] [DecidableEq D]

variable [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]

variable [Fintype Z] [DecidableEq Z]

/-- NODE paper:1504.00233#1.lossless
§1.2: exact lossless memory, arXiv:1504.00233v5, PDF p.12. -/
theorem lossless_memory [Nonempty X] (p : X → ℝ) (hp : paperProbability p) :
    let k := Nat.ceil (Real.logb 2 ((Finset.univ.filter (fun x => 0 < p x)).card:ℝ))
    (∃ c : paperSourceCode X (2^k), ∀ x, 0 < p x → c.decode (c.encode x) = x) ∧
    ∀ m : ℕ, (∃ c : paperSourceCode X (2^m), ∀ x, 0 < p x → c.decode (c.encode x) = x) → k ≤ m := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P07

end
