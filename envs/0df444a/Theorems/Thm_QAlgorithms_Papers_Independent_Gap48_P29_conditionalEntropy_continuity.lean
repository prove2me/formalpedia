-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P29_conditionalEntropy_continuity
-- name    : QAlgorithms.Papers.Independent.Gap48.P29.conditionalEntropy_continuity
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T04:13:51.904966+00:00
-- url     : https://prove2.me/theorems/35e6c7b4-b60a-4b24-808e-ae5242df4837
-- title:
--   Conditional-entropy continuity with the printed marginal
-- statement:
--   Let $R$ and $Q$ each have the same positive finite dimension $d$, and let $\rho$ and $\sigma$ be density operators on $R\otimes Q$. Put $\rho_Q=\operatorname{tr}_R\rho$ and $\sigma_Q=\operatorname{tr}_R\sigma$. If squared Uhlmann fidelity satisfies $F(\rho,\sigma)>5/9$, then
--
--   $$|[S(\rho)-S(\rho_Q)]-[S(\sigma)-S(\sigma_Q)]|\leq6\sqrt{1-F(\rho,\sigma)}\log_2d+2.$$
--
--   The paper calls the joint entropy minus this Q marginal $S(Q\mid R)$; the displayed quantity fixes the intended convention.
-- source:
--   On Quantum Fidelities and Channel Capacities, arXiv:quant-ph/9809010v1, PDF p. 6, Lemma 7, Eq.(48), continuing p.6

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P29

noncomputable section

namespace QAlgorithms.Papers.Independent.Gap48.P29

open QAlgorithms Filter

open scoped Matrix ComplexConjugate ComplexOrder Topology

open QAlgorithms.Papers.Independent.Information100.P07 (IsProjection)

open QAlgorithms.Papers.Independent.Information100.P67 (squaredFidelity)

/-- PDF pp.5--6, Lemma 7, Eq.(48): joint entropy minus the Q marginal, exactly as
printed (the paper calls this S(Q|R)). R and Q have the same dimension. -/
theorem conditionalEntropy_continuity {d : ℕ} (hd : 0 < d)
    (rho sigma : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)
    (hrho : IsDensityMatrix rho) (hsigma : IsDensityMatrix sigma)
    (hclose : (5 : ℝ) / 9 < squaredFidelity rho sigma) :
    |(vnEntropy rho - vnEntropy (traceLeft rho)) -
      (vnEntropy sigma - vnEntropy (traceLeft sigma))| ≤
      6 * Real.sqrt (1 - squaredFidelity rho sigma) * Real.logb 2 (d : ℝ) + 2 := by sorry

end QAlgorithms.Papers.Independent.Gap48.P29

end
