-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P17_sifting_surplus
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P17.sifting_surplus
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T04:20:32.973257+00:00
-- url     : https://prove2.me/theorems/020d7723-189f-476f-9d92-4570b35aeab5
-- title:
--   Positive signal surplus yields enough matching bases with probability tending to one
-- statement:
--   Fix an overhead $\gamma>0$ and let $N_n=\lceil(4+\gamma)n\rceil$. Assume all $N_n$ ideal signals are received. Alice and Bob independently choose uniform strings $A,B\in\{0,1\}^{N_n}$ specifying their preparation and measurement bases. Let $M(A,B)=|\{i:A_i=B_i\}|$. Then
--
--   $$
--   \lim_{n\to\infty}\Pr[M(A,B)\ge2n]=1.
--   $$
--
--   Here the probability is the explicit uniform average over all ordered pairs $(A,B)$, and a shortage of matches is an abort. This gives the sifting surplus in Protocol 3, step 6; it concerns matching bases, not the later error test.
--
--   **Formalization Note** The integer ceiling implements the source's signal count and agrees with it whenever $(4+\gamma)n$ is integral. The overhead is called $\gamma$ to distinguish it from an error threshold.
-- source:
--   Simple Proof of Security of the BB84 Quantum Key Distribution Protocol, arXiv:quant-ph/0003004v2, PDF p. 4, Protocol 3 step 6: enough matching bases with high probability

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P17

namespace QAlgorithms.Papers.Independent.Intakenext100.P17

noncomputable section

open scoped ComplexConjugate

open Classical

open QAlgorithms.DopedTomography (bellVector)

open QAlgorithms.Papers.Independent.Support50.P04 (BinaryWord)

/-- PDF p.4, Protocol 3 step 6: for each fixed positive surplus gamma, the
probability that at least 2n matching-basis positions remain tends to one.
Only ideal receipt and independent uniform bases enter this combinatorial
statement. It does not assert acceptance of the subsequent error test. -/
theorem sifting_surplus (gamma : ℝ) (hgamma : 0 < gamma) :
    Filter.Tendsto (fun n : ℕ => siftingSuccess n (signalCount gamma n))
      Filter.atTop (nhds (1 : ℝ)) := by sorry

end

end QAlgorithms.Papers.Independent.Intakenext100.P17
