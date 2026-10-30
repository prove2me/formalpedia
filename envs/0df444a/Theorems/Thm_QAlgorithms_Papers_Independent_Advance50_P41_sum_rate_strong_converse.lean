-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P41_sum_rate_strong_converse
-- name    : QAlgorithms.Papers.Independent.Advance50.P41.sum_rate_strong_converse
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T09:14:27.609846+00:00
-- url     : https://prove2.me/theorems/e35062c8-fb57-4119-96fd-c179c54bb6e7
-- title:
--   Strong converse for the combined consumed resources
-- statement:
--   Let $\mathcal E=\{p(x),|\psi_x\rangle^A\otimes|\sigma_x\rangle^C\}$ be a countably supported ensemble with strictly positive probabilities summing to one and normalized pure vectors on finite-dimensional complex systems $A,C$. Let $Y=y(X)$ be the canonical orthogonal irreducible-component label of the joint $AC$ ensemble. Entropies $S$ use base-two logarithms and refer to the resulting source and its canonical $Y$ extension.
--
--   A block code uses arbitrary CPTP maps $A^nC^nA_0\to\widehat C^nM$ and $MB_0\to\widehat A^n$, fixed independently of the inaccessible input word, and an initial maximally entangled state of local dimension $K_n\ge1$. For every positive block length $n$, $1\le d_n=\dim M\le(\dim A)^n$. Write $Q_n=\log_2 d_n/n$, $E_n=\log_2 K_n/n$, and $F_n$ for the average joint root fidelity with the original $A^nC^n$ letters.
--
--   For every actual code sequence and real $r$,
--   $$Q_n+E_n\longrightarrow r<S(A)\quad\Longrightarrow\quad F_n\longrightarrow0.$$
--   No fidelity convergence or success premise is assumed; separate convergence of $Q_n$ and $E_n$ is unnecessary.
--
--   This is the strong converse for the combined-resource lower bound. The separate quantum-rate strong-converse questions on page 6 remain open.
-- source:
--   Entanglement-Assisted Quantum Data Compression, arXiv:1901.06346v1, PDF p. 5, Discussion, continued p.6

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P41

noncomputable section

namespace QAlgorithms.Papers.Independent.Advance50.P41

open Filter

open scoped Topology BigOperators Matrix ComplexConjugate

attribute [local instance] Classical.propDecidable Classical.decEq

variable {X A C : Type} [Fintype A] [Fintype C]

/-- Discussion, PDF pp.5,6: strong converse for the combined consumed
resources. No success assumption is made; fidelity tends to ZERO below S(A).
Separate quantum-rate strong converses are open questions in the source. -/
theorem sum_rate_strong_converse [Countable X] (s : ProductPureSource X A C) (hs : s.Valid)
    (P : QuantumCodeSequence A C) (r : ℝ) (hr : r < s.entropyA)
    (hlimit : Tendsto (fun n => (P n).quantumRate + (P n).entanglementRate)
      atTop (nhds r)) :
    Tendsto (fun n => (P n).fidelity s) atTop (nhds 0) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P41

end
