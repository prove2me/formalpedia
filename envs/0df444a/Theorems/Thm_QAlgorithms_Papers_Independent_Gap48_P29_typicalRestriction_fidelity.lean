-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P29_typicalRestriction_fidelity
-- name    : QAlgorithms.Papers.Independent.Gap48.P29.typicalRestriction_fidelity
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T04:15:28.78027+00:00
-- url     : https://prove2.me/theorems/5375dd6b-bed4-4604-9c3e-8167d9e1c73e
-- title:
--   Replacing a source by its normalized typical restriction
-- statement:
--   Let $\Sigma=\{\rho_n\}$ be a source on tensor powers of a fixed nonzero finite-dimensional Hilbert space, satisfying the quantum asymptotic equipartition property (QAEP). Its entropy rate is $s=\limsup_n S(\rho_n)/n$, in bits. No independence or identical-distribution hypothesis is imposed. For a fixed window $w>0$, let $P_{n,w}$ be the full spectral projector of $\rho_n$ for eigenvalues in $[2^{-n(s+w)},2^{-n(s-w)}]$, including their multiplicities, and put $t_{n,w}=\operatorname{tr}(P_{n,w}\rho_nP_{n,w})$. Let $n\geq1$ and $0\leq\delta<1$ satisfy $t_{n,w}\geq1-\delta$, and let $\mathcal E$ be a trace-preserving operation on that block. The normalized typical restriction $\widehat\rho_{n,w}=P_{n,w}\rho_nP_{n,w}/t_{n,w}$ is well defined and satisfies
--
--   $$|F_e(\widehat\rho_{n,w},\mathcal E)-F_e(\rho_n,\mathcal E)|\leq\frac{4\delta}{(1-\delta)^2}.$$
--
--   QAEP supplies the required mass bound eventually for every positive tolerance.
-- source:
--   On Quantum Fidelities and Channel Capacities, arXiv:quant-ph/9809010v1, PDF p. 6, Lemma 9, Eqs.(52)–(54)

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P29

noncomputable section

namespace QAlgorithms.Papers.Independent.Gap48.P29

open QAlgorithms Filter

open scoped Matrix ComplexConjugate ComplexOrder Topology

open QAlgorithms.Papers.Independent.Information100.P07 (IsProjection)

open QAlgorithms.Papers.Independent.Information100.P67 (squaredFidelity)

/-- PDF p.6, Lemma 9, Eqs.(52)--(54): distinct spectral-window and discarded-mass
parameters. delta<1 makes the retained trace strictly positive before normalization. -/
theorem typicalRestriction_fidelity (S : BlockQuantumSource) (hS : QAEP S)
    (window : ℝ) (hwindow : 0 < window) (n : ℕ) (hn : 0 < n)
    (delta : ℝ) (hdelta0 : 0 ≤ delta) (hdelta1 : delta < 1)
    (hmass : 1 - delta ≤ qaepRetainedMass S window n)
    (E : Superop (SourceRegister S.dimension n) (SourceRegister S.dimension n)) (hE : IsChannel E) :
    |fe (typicalRestriction S window n) E - fe (S.rho n) E| ≤
      4 * delta / (1 - delta) ^ 2 := by sorry

end QAlgorithms.Papers.Independent.Gap48.P29

end
