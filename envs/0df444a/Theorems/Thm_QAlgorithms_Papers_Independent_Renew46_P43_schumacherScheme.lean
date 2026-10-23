-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P43_schumacherScheme
-- name    : QAlgorithms.Papers.Independent.Renew46.P43.schumacherScheme
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-22T06:27:59.140681+00:00
-- url     : https://prove2.me/theorems/4da7529b-b143-4f2d-b6d5-c5f9904cdc18
-- title:
--   Theorem I.16: Schumacher code rate≤H(averageState)+Kd alpha/sqrt(n); Fe≥1−4N e^(−2mu²alpha²).
-- statement:
--   Let a finite pure-state iid source have average $\bar\rho$ on a nonzero finite system of Hilbert dimension $d$. Compression spaces and block lengths are positive, decoders are CPTP and all entropies/rates are in bits. The fixed-error rates are limsups of the actual block minimum of $\log_2\dim\mathcal K/n$. Quantum encoding requires a CPTP extension; arbitrary encoding is state valued. In finite-block bounds $\alpha>0$, $K_V=2\log_2(e)/e$, and $N,\mu$ are the support rank and least positive eigenvalue of $\sqrt{\bar\rho(1-\bar\rho)}$. The Schumacher code compresses onto the nonzero variance-typical range and decodes by inclusion; the strong converse permits any arbitrary-encoding code of fidelity error at most $\lambda$. For the intrinsic version the source letters and decoder lie in the specified classical, hybrid or full matrix algebra, with its intrinsic trace.
--
--   $$
--   R\le H(\bar\rho)+K_Vd\alpha/\sqrt n,\qquad F_e\ge1-4N(\bar\rho)e^{-2\mu(\bar\rho)^2\alpha^2}.
--   $$
--
--   This is the source result with its stated operational or information-theoretic domain.
-- source:
--   Coding Theorems of Quantum Information Theory, arXiv:quant-ph/9907077v1, PDF p. 16, Theorem I.16

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P43

noncomputable section

namespace QAlgorithms.Papers.Independent.Renew46.P43

open scoped BigOperators Matrix ComplexConjugate ComplexOrder ENNReal Matrix.Norms.L2Operator

open Filter MeasureTheory

open QAlgorithms.Papers.Independent.Information100.P08 (IsPure)

open QAlgorithms.Papers.Independent.Information100.P06 (Below)

open QAlgorithms.Papers.Independent.Information100.P60 (copies relativeBits)

open QAlgorithms.Papers.Independent.Dependency50.P19 (count both)

open QAlgorithms.Papers.Independent.Information100.P22 (coherentInformation)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Theorem I.16, PDF p.16: the actual range compression followed by inclusion.
The code's range is required nonzero: the printed encoder divides by dim K. -/
theorem schumacherScheme {a d : ℕ} (S : PureSource a d) (spectral : FineResolution d)
    (haverage : spectral.state = S.average) (n : ℕ) (hn : 0 < n)
    (alpha : ℝ) (halpha : 0 < alpha) (k : ℕ) (hk : 0 < k)
    (V : Matrix (Fin n → Fin d) (Fin k) ℂ)
    (hisometry : Vᴴ * V = 1) (hrange : V * Vᴴ = varianceProjector spectral n alpha) :
    Real.logb 2 k / n ≤ vnEntropy S.average + varianceConstant * d * alpha / Real.sqrt n ∧
    sourceFe (copies n S.average) (conjSuperop V ∘ projectionEncoder V) ≥
      1 - 2 * varianceTail spectral alpha := by sorry

end QAlgorithms.Papers.Independent.Renew46.P43

end
