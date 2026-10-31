-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P07_classical_compression_direct
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P07.classical_compression_direct
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T04:37:03.64058+00:00
-- url     : https://prove2.me/theorems/aa05f365-b6e2-41b6-9537-9fa01bf8a811
-- title:
--   §1.2 (1.2): classical Rényi compression direct bound
-- statement:
--   Let $p$ be a probability law on a finite nonempty alphabet $X$. A code consists of an encoder into an alphabet of $m\ge1$ symbols and a decoder, and its error is the probability of recovering the wrong source symbol. Logs are binary, and $H(p)$ is Shannon entropy. Introductory smooth max-entropy minimizes the order-$1/2$ Rényi entropy over normalized probability laws within variational distance $\varepsilon$.
--
--   For finite probability source X, 0<ε<1, positive integer m, and some α∈[1/2,1), log2 m≥Hα(X)+α/(1−α)log2(1/ε) implies an (ε,m)-code. α=1/2 is included in the PDF interval.
--
--   $$
--   \log_2m\ge H_\alpha(p)+\frac{\alpha}{1-\alpha}\log_2\frac1\varepsilon\quad\Longrightarrow\quad\exists\text{ an }(\varepsilon,m)\text{-code}.
--   $$
--
--   This result records the source’s operational or structural relation, with the stated endpoint and attainment clauses retained.
-- source:
--   Quantum Information Processing with Finite Resources -- Mathematical Foundations, arXiv:1504.00233v5, PDF p. 13, §1.2 (1.2): classical Rényi compression direct bound

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

/-- NODE paper:1504.00233#1.direct
§1.2 (1.2): classical Rényi compression direct bound, arXiv:1504.00233v5, PDF p.13. -/
theorem classical_compression_direct [Nonempty X] (p : X → ℝ) (hp : paperProbability p) (e : ℝ) (he : 0 < e) (he1 : e < 1)
    (m : ℕ) (hm : 0 < m) (a : ℝ) (ha : 1/2 ≤ a) (ha1 : a < 1)
    (hsize : paperClassicalRenyi p a+a/(1-a)*Real.logb 2 (1/e) ≤ Real.logb 2 m) :
    ∃ c : paperSourceCode X m, paperCodeError p c ≤ e := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P07

end
