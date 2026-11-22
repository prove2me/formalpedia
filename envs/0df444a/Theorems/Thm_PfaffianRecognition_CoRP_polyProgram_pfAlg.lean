-- Prove2me | Theorems.Thm_PfaffianRecognition_CoRP_polyProgram_pfAlg
-- name    : PfaffianRecognition.CoRP.polyProgram_pfAlg
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-22T21:25:06.746915+00:00
-- url     : https://prove2.me/theorems/0135ca86-36a0-4bee-b765-6f86875c5919
-- title:
--   The randomized Pfaffian recognition algorithm runs in polynomial time
-- statement:
--   The randomized Pfaffian recognition algorithm $\mathcal A(\rho,w)$ is computed by a single polynomial-time Boolean-stack Turing program.
--
--   Here $\mathcal A$ is the algorithm of the definition `PfaffianRecognition_CoRP_Algorithm`: on a random string $\rho$ and a graph encoding $w$ it parses $w$, and runs $|E|+3$ rounds, each consisting of Gaussian elimination over $\mathbb F_2$, the evaluation of the wrong-sign expression
--   $$Q(\beta)=s\,\Phi(\beta)+\sum_{d_e=1}\Phi(\beta^{(e)})+\sum_{\{e,f\}\text{ crossing}}\Phi(\beta^{(e,f)})$$
--   through determinants over $\mathbb F_{2^{2m}}$ (with $m=3^{\lceil\log_2(N+1)\rceil}=O(N^2)$), and a greedy matching search. The statement asserts that one fixed machine computes $\mathcal A(\rho,w)$ from the pair $(\rho,w)$ within a number of steps bounded by a fixed polynomial in $|\rho|+|w|$.
--
--   This is the running-time half of the headline algorithm (Theorem 1.1): polynomially many determinant evaluations on matrices of order at most $N$, as in the proof of Theorem 3.2.
--
--   **Formalization Note** The input is `encodePair id id (ρ, w)` and the output `encodeBool`, in the conventions of the Boolean-stack machine library `QuantumMaxCutFiniteNumericRuntime`.
-- source:
--   Priyanshu Pant, Ranveer Singh, Pfaffian Recognition is in coRP, STOC 2027 submission #858 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/858.pdf, Theorem 1.1 (p. 3), proof of Theorem 3.2 (p. 7): polynomially many determinant computations, field operations in polynomial time

import Definitions.Def_PfaffianRecognition_CoRP_Algorithm
import Definitions.Def_QuantumMaxCutFiniteNumericRuntime

namespace PfaffianRecognition.CoRP

open OAI.MetricKMedian.Binary in
theorem polyProgram_pfAlg : Nonempty (PolyProgram (encodePair id id) encodeBool pfAlg) := by sorry

end PfaffianRecognition.CoRP
