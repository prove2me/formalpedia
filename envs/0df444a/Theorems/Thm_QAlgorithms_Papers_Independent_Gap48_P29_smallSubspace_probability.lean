-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P29_smallSubspace_probability
-- name    : QAlgorithms.Papers.Independent.Gap48.P29.smallSubspace_probability
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T04:23:51.707076+00:00
-- url     : https://prove2.me/theorems/39f9689c-8ce9-4e57-b111-f4eb8e466cb9
-- title:
--   Small-subspace probability bound
-- statement:
--   Let $\Sigma=\{\rho_n\}$ be a source on tensor powers of a fixed nonzero finite-dimensional Hilbert space, satisfying the quantum asymptotic equipartition property (QAEP). Its entropy rate is $s=\limsup_n S(\rho_n)/n$, in bits. No independence or identical-distribution hypothesis is imposed. For every $w>0$ and $\delta>0$, there is a threshold after which every orthogonal projector $P$ on the source block satisfying $\dim\operatorname{ran}P<(1-\delta)2^{n(s-w)}$ obeys
--
--   $$\operatorname{tr}(P\rho_n)\leq\delta.$$
--
--   The threshold is uniform over all such projectors and may differ from that used for the typical-mass bound at the same tolerances. This is the background assertion cited to [30].
-- source:
--   On Quantum Fidelities and Channel Capacities, arXiv:quant-ph/9809010v1, PDF p. 3, Eq.(23), cited background [30]

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P29

noncomputable section

namespace QAlgorithms.Papers.Independent.Gap48.P29

open QAlgorithms Filter

open scoped Matrix ComplexConjugate ComplexOrder Topology

open QAlgorithms.Papers.Independent.Information100.P07 (IsProjection)

open QAlgorithms.Papers.Independent.Information100.P67 (squaredFidelity)

/-- PDF p.3, Eq.(23), cited background [30]: an eventual statement with its own
threshold, uniform over all small subspaces at each sufficiently large block size. -/
theorem smallSubspace_probability (S : BlockQuantumSource) (hS : QAEP S)
    (window delta : ℝ) (hwindow : 0 < window) (hdelta : 0 < delta) :
    ∀ᶠ n : ℕ in atTop, ∀ P : Matrix (SourceRegister S.dimension n) (SourceRegister S.dimension n) ℂ,
      IsProjection P →
      (projectionDimension P : ℝ) <
        (1 - delta) * (2 : ℝ) ^ ((n : ℝ) * (sourceEntropyRate S - window)) →
      (P * S.rho n).trace.re ≤ delta := by sorry

end QAlgorithms.Papers.Independent.Gap48.P29

end
