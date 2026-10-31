-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P07_classical_smooth_aep
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P07.classical_smooth_aep
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T04:38:59.77113+00:00
-- url     : https://prove2.me/theorems/57f7a8b7-ba29-409b-a078-b66192ed6657
-- title:
--   §1.2 (1.8): classical smoothed max-entropy AEP
-- statement:
--   Let $p$ be a probability law on a finite nonempty alphabet $X$. A code consists of an encoder into an alphabet of $m\ge1$ symbols and a decoder, and its error is the probability of recovering the wrong source symbol. Logs are binary, and $H(p)$ is Shannon entropy. Introductory smooth max-entropy minimizes the order-$1/2$ Rényi entropy over normalized probability laws within variational distance $\varepsilon$.
--
--   For iid finite sources and fixed 0<εprime<1, normalized-distribution variational smoothing of the classical order-1/2 entropy has (1/n)Hmax^εprime(X^n)→H(Y).
--
--   $$
--   \lim_{n\to\infty}\frac1n H_{\max}^{\varepsilon}(p^{\otimes n})=H(p),\qquad0<\varepsilon<1.
--   $$
--
--   This result records the source’s operational or structural relation, with the stated endpoint and attainment clauses retained.
-- source:
--   Quantum Information Processing with Finite Resources -- Mathematical Foundations, arXiv:1504.00233v5, PDF p. 14, §1.2 (1.8): classical smoothed max-entropy AEP

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

/-- NODE paper:1504.00233#1.classicalaep
§1.2 (1.8): classical smoothed max-entropy AEP, arXiv:1504.00233v5, PDF p.14. -/
theorem classical_smooth_aep [Nonempty X] (p : X → ℝ) (hp : paperProbability p) (e : ℝ) (he : 0 < e) (he1 : e < 1) :
    Tendsto (fun n : ℕ => introSmoothMax (iidLaw p n) e/(n:ℝ)) atTop (nhds (paperShannon p)) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P07

end
