-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P29_typicalCompression_fidelity
-- name    : QAlgorithms.Papers.Independent.Gap48.P29.typicalCompression_fidelity
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-22T04:14:43.46017+00:00
-- url     : https://prove2.me/theorems/f8bc6e3f-9f6a-4eac-8902-d00006cf70d5
-- title:
--   Effect of typical-subspace compression
-- statement:
--   Let $\Sigma=\{\rho_n\}$ be a source on tensor powers of a fixed nonzero finite-dimensional Hilbert space, satisfying the quantum asymptotic equipartition property (QAEP). Its entropy rate is $s=\limsup_n S(\rho_n)/n$, in bits. No independence or identical-distribution hypothesis is imposed. For a fixed window $w>0$, let $P_{n,w}$ be the full spectral projector of $\rho_n$ for eigenvalues in $[2^{-n(s+w)},2^{-n(s-w)}]$, including their multiplicities, and put $t_{n,w}=\operatorname{tr}(P_{n,w}\rho_nP_{n,w})$. Let $n\geq1$, let $\mathcal C_n$ be a trace-preserving compression into the typical subspace with a Kraus branch $X\mapsto P_{n,w}XP_{n,w}$ and a CP residual branch, and let $\mathcal A_n$ be any trace-preserving operation on the source block. Then
--
--   $$|F_e(\rho_n,\mathcal A_n\mathcal C_n)-F_e(\rho_n,\mathcal A_n)|\leq2(1-t_{n,w}).$$
--
--   This compares transmission with and without the specified compression step.
-- source:
--   On Quantum Fidelities and Channel Capacities, arXiv:quant-ph/9809010v1, PDF p. 6, Lemma 8, Eqs.(50)–(51)

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P29

noncomputable section

namespace QAlgorithms.Papers.Independent.Gap48.P29

open QAlgorithms Filter

open scoped Matrix ComplexConjugate ComplexOrder Topology

open QAlgorithms.Papers.Independent.Information100.P07 (IsProjection)

open QAlgorithms.Papers.Independent.Information100.P67 (squaredFidelity)

/-- PDF p.6, Lemma 8, Eq.(51). Source correction: printed strict < becomes ≤;
zero discarded mass is allowed and would otherwise require 0<0. The CP residual
and spectral projection structure, rather than the false general Lemma 3, are retained. -/
theorem typicalCompression_fidelity (S : BlockQuantumSource) (hS : QAEP S)
    (window : ℝ) (hwindow : 0 < window) (n : ℕ) (hn : 0 < n)
    (C A : Superop (SourceRegister S.dimension n) (SourceRegister S.dimension n))
    (hC : IsCompression (qaepSpectralProjector S window n) C) (hA : IsChannel A) :
    |fe (S.rho n) (A ∘ C) - fe (S.rho n) A| ≤
      2 * (1 - qaepRetainedMass S window n) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P29

end
