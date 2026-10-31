-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P07_classical_source_coding
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P07.classical_source_coding
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T04:37:39.439175+00:00
-- url     : https://prove2.me/theorems/2901a42a-de5d-4181-bf02-60a867d37dbe
-- title:
--   §1.2 (1.5): source coding and strong converse
-- statement:
--   Let $p$ be a probability law on a finite nonempty alphabet $X$. A code consists of an encoder into an alphabet of $m\ge1$ symbols and a decoder, and its error is the probability of recovering the wrong source symbol. Logs are binary, and $H(p)$ is Shannon entropy. Introductory smooth max-entropy minimizes the order-$1/2$ Rényi entropy over normalized probability laws within variational distance $\varepsilon$.
--
--   For iid finite source law τ and a fixed error in (0,1), any rate R>H(τ) admits codes for all sufficiently large n; rates below H(τ) have failure probability tending to one. Cardinalities must be rounded to integers rather than using Fin(2^(nR)) for arbitrary real R).
--
--   $$
--   R>H(p)\Longrightarrow\text{eventually an }(\varepsilon,\lceil2^{nR}\rceil)\text{-code exists};\quad R<H(p)\Longrightarrow\Pr[\text{decoding fails}]\to1.
--   $$
--
--   This result records the source’s operational or structural relation, with the stated endpoint and attainment clauses retained.
-- source:
--   Quantum Information Processing with Finite Resources -- Mathematical Foundations, arXiv:1504.00233v5, PDF p. 13, §1.2 (1.5): source coding and strong converse

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

/-- NODE paper:1504.00233#1.shannon
§1.2 (1.5): source coding and strong converse, arXiv:1504.00233v5, PDF p.13. -/
theorem classical_source_coding [Nonempty X] (p : X → ℝ) (hp : paperProbability p) (R : ℝ) (hR : 0 ≤ R) :
    (paperShannon p < R → ∀ e : ℝ, 0 < e → e < 1 → ∃ N : ℕ, ∀ n ≥ N,
      ∃ c : paperSourceCode (Fin n → X) (codeCardinality n R), paperCodeError (iidLaw p n) c ≤ e) ∧
    (R < paperShannon p → ∀ codes : (n : ℕ) → paperSourceCode (Fin n → X) (codeCardinality n R),
      Tendsto (fun n => paperCodeError (iidLaw p n) (codes n)) atTop (nhds 1)) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P07

end
