-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P40_relativeEntropyImpliesTraceApproximation
-- name    : QAlgorithms.Papers.Independent.Gap48.P40.relativeEntropyImpliesTraceApproximation
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-22T05:33:31.45291+00:00
-- url     : https://prove2.me/theorems/a4840196-d25d-46c7-84e8-2fd23478da58
-- title:
--   §VIII, Theorem 7 first implication (58)
-- statement:
--   All matrices act on a complex Hilbert space of positive finite dimension $d$. A state is positive semidefinite with trace one. All logarithms are natural, and $D(\rho\|\sigma)$ denotes support-aware Umegaki relative entropy, with value $+\infty$ when support containment fails. Fix a state $\rho$ on a positive finite-dimensional Hilbert space $\mathcal H$, and let $\sigma_n$ be a state on $\mathcal H^{\otimes n}$ for each positive integer $n$. Then
--
--   $$
--   D(\rho^{\otimes n}\|\sigma_n)\longrightarrow0\quad\Longrightarrow\quad\|\rho^{\otimes n}-\sigma_n\|_1\longrightarrow0.
--   $$
--
--   This is exactly the forward implication (58). The full theorem, including its defective converse, has a separate deferral record.
-- source:
--   Continuity bounds on the quantum relative entropy, arXiv:quant-ph/0503218v3, PDF p. 12, §VIII, Theorem 7 first implication (58)

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P40

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder Topology Matrix.Norms.L2Operator

open Filter MeasureTheory Asymptotics

open QAlgorithms

open QAlgorithms.Papers.Independent.Dependency50.P21 (relativeEntropy)

open QAlgorithms.Papers.Independent.Information100.P50 (IsUINorm)

open QAlgorithms.Papers.Independent.Information100.P56 (entropy)

open QAlgorithms.Papers.Independent.Information100.P60 (copies)

open QAlgorithms.Papers.Independent.Information100.P44 (Mat)

namespace QAlgorithms.Papers.Independent.Gap48.P40

/-- PDF p.12, Theorem 7, first implication (58) only. Positive copy counts
are k+1; sigma is normalized on the full tensor power. The converse is deferred. -/
theorem relativeEntropyImpliesTraceApproximation {d : ℕ} (hd : 0 < d)
    (rho : Mat d) (hrho : IsDensityMatrix rho)
    (sigma : (k : ℕ) → Matrix (Fin (k + 1) → Fin d) (Fin (k + 1) → Fin d) ℂ)
    (hsigma : ∀ k, IsDensityMatrix (sigma k))
    (hlimit : Tendsto (fun k => relativeEntropy (copies (k + 1) rho) (sigma k))
      atTop (nhds (0 : EReal))) :
    Tendsto (fun k => traceNorm (copies (k + 1) rho - sigma k)) atTop (nhds (0 : ℝ)) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P40

end
