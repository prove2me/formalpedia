-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P29_typicalRestriction_reliability
-- name    : QAlgorithms.Papers.Independent.Gap48.P29.typicalRestriction_reliability
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T04:24:43.934684+00:00
-- url     : https://prove2.me/theorems/e20375c6-e9c4-4a25-93ae-101bd458af98
-- title:
--   Equivalence of typical-source and full-source reliability
-- statement:
--   Let $\Sigma=\{\rho_n\}$ be a source on tensor powers of a fixed nonzero finite-dimensional Hilbert space, satisfying the quantum asymptotic equipartition property (QAEP). Its entropy rate is $s=\limsup_n S(\rho_n)/n$, in bits. No independence or identical-distribution hypothesis is imposed. For a fixed window $w>0$, let $P_{n,w}$ be the full spectral projector of $\rho_n$ for eigenvalues in $[2^{-n(s+w)},2^{-n(s-w)}]$, including their multiplicities, and put $t_{n,w}=\operatorname{tr}(P_{n,w}\rho_nP_{n,w})$. Let $\mathcal A_n$ be any sequence of trace-preserving operations on the source blocks and let $\widehat\rho_{n,w}=P_{n,w}\rho_nP_{n,w}/t_{n,w}$ whenever the retained mass is positive, as it is eventually. Then
--
--   $$F_e(\rho_n,\mathcal A_n)\longrightarrow1\quad\Longleftrightarrow\quad F_e(\widehat\rho_{n,w},\mathcal A_n)\longrightarrow1.$$
--
--   This concerns normalized typical density operators, rather than minimum fidelity over pure states in the typical subspace.
-- source:
--   On Quantum Fidelities and Channel Capacities, arXiv:quant-ph/9809010v1, PDF p. 6, Section IV conclusion

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P29

noncomputable section

namespace QAlgorithms.Papers.Independent.Gap48.P29

open QAlgorithms Filter

open scoped Matrix ComplexConjugate ComplexOrder Topology

open QAlgorithms.Papers.Independent.Information100.P07 (IsProjection)

open QAlgorithms.Papers.Independent.Information100.P67 (squaredFidelity)

/-- PDF p.6, conclusion of section IV: full-source reliability is equivalent to
reliability for its normalized typical restrictions, for any fixed positive window.
This is not a minimum-pure-state assertion. -/
theorem typicalRestriction_reliability (S : BlockQuantumSource) (hS : QAEP S)
    (window : ℝ) (hwindow : 0 < window)
    (A : (n : ℕ) → Superop (SourceRegister S.dimension n) (SourceRegister S.dimension n))
    (hA : ∀ n, IsChannel (A n)) :
    (Tendsto (fun n => fe (S.rho n) (A n)) atTop (nhds 1) ↔
      Tendsto (fun n => fe (typicalRestriction S window n) (A n)) atTop (nhds 1)) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P29

end
