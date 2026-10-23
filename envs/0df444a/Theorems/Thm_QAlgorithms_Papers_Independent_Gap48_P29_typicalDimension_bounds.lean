-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P29_typicalDimension_bounds
-- name    : QAlgorithms.Papers.Independent.Gap48.P29.typicalDimension_bounds
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-22T04:22:59.453027+00:00
-- url     : https://prove2.me/theorems/04b11a77-d06a-45a8-9f26-d31970ecf32a
-- title:
--   Typical-subspace dimension bounds
-- statement:
--   Let $\Sigma=\{\rho_n\}$ be a source on tensor powers of a fixed nonzero finite-dimensional Hilbert space, satisfying the quantum asymptotic equipartition property (QAEP). Its entropy rate is $s=\limsup_n S(\rho_n)/n$, in bits. No independence or identical-distribution hypothesis is imposed. For a fixed window $w>0$, let $P_{n,w}$ be the full spectral projector of $\rho_n$ for eigenvalues in $[2^{-n(s+w)},2^{-n(s-w)}]$, including their multiplicities, and put $t_{n,w}=\operatorname{tr}(P_{n,w}\rho_nP_{n,w})$. For $\delta>0$ and every positive $n$ with $t_{n,w}>1-\delta$,
--
--   $$(1-\delta)2^{n(s-w)}\leq\dim\operatorname{ran}P_{n,w}\leq2^{n(s+w)}.$$
--
--   The dimension is the rank of the actual spectral subspace, including eigenvalue multiplicities. QAEP ensures the mass hypothesis eventually.
-- source:
--   On Quantum Fidelities and Channel Capacities, arXiv:quant-ph/9809010v1, PDF p. 3, Eq.(22)

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P29

noncomputable section

namespace QAlgorithms.Papers.Independent.Gap48.P29

open QAlgorithms Filter

open scoped Matrix ComplexConjugate ComplexOrder Topology

open QAlgorithms.Papers.Independent.Information100.P07 (IsProjection)

open QAlgorithms.Papers.Independent.Information100.P67 (squaredFidelity)

/-- PDF p.3, Eq.(22): both bounds on the actual spectral-subspace dimension, at
every positive block length where the displayed QAEP mass bound is satisfied. -/
theorem typicalDimension_bounds (S : BlockQuantumSource) (hS : QAEP S)
    (window delta : ℝ) (hwindow : 0 < window) (hdelta : 0 < delta)
    (n : ℕ) (hn : 0 < n) (hmass : 1 - delta < qaepRetainedMass S window n) :
    (1 - delta) * (2 : ℝ) ^ ((n : ℝ) * (sourceEntropyRate S - window)) ≤
      (projectionDimension (qaepSpectralProjector S window n) : ℝ) ∧
    (projectionDimension (qaepSpectralProjector S window n) : ℝ) ≤
      (2 : ℝ) ^ ((n : ℝ) * (sourceEntropyRate S + window)) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P29

end
