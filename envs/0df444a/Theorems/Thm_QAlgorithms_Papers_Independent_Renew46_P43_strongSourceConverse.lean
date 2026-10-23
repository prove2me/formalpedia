-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P43_strongSourceConverse
-- name    : QAlgorithms.Papers.Independent.Renew46.P43.strongSourceConverse
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-22T06:30:03.846457+00:00
-- url     : https://prove2.me/theorems/9ee1088b-6210-427b-84a5-dc7cff836d12
-- title:
--   Theorem I.19: dim K≥(1−lambda−4sqrt(N) e^(−mu²alpha²))2^(nH(averageState)−Kd alpha sqrt(n)), for any arbitrary-encoding (n,lambda)Fbar code and
-- statement:
--   Let a finite pure-state iid source have average $\bar\rho$ on a nonzero finite system of Hilbert dimension $d$. Compression spaces and block lengths are positive, decoders are CPTP and all entropies/rates are in bits. The fixed-error rates are limsups of the actual block minimum of $\log_2\dim\mathcal K/n$. Quantum encoding requires a CPTP extension; arbitrary encoding is state valued. In finite-block bounds $\alpha>0$, $K_V=2\log_2(e)/e$, and $N,\mu$ are the support rank and least positive eigenvalue of $\sqrt{\bar\rho(1-\bar\rho)}$. The Schumacher code compresses onto the nonzero variance-typical range and decodes by inclusion; the strong converse permits any arbitrary-encoding code of fidelity error at most $\lambda$. For the intrinsic version the source letters and decoder lie in the specified classical, hybrid or full matrix algebra, with its intrinsic trace.
--
--   $$
--   \dim\mathcal K\ge\bigl(1-\lambda-4\sqrt{N(\bar\rho)}e^{-\mu(\bar\rho)^2\alpha^2}\bigr)2^{nH(\bar\rho)-K_Vd\alpha\sqrt n}.
--   $$
--
--   This is the source result with its stated operational or information-theoretic domain.
-- source:
--   Coding Theorems of Quantum Information Theory, arXiv:quant-ph/9907077v1, PDF p. 19, Theorem I.19

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

/-- Theorem I.19, PDF pp.19-20. sqrt covers N alone; decoder is any CPTP map. -/
theorem strongSourceConverse {a d n : ℕ} (S : PureSource a d) (spectral : FineResolution d)
    (haverage : spectral.state = S.average) (c : SourceCode S n)
    (lambda alpha : ℝ) (hcode : 1 - c.fidelity ≤ lambda) (halpha : 0 < alpha) :
    (c.dim : ℝ) ≥
      (1 - lambda - 4 * Real.sqrt (spectralN spectral) *
        Real.exp (-(spectralMu spectral)^2 * alpha^2)) *
      exp2 (n * vnEntropy S.average - varianceConstant * d * alpha * Real.sqrt n) := by sorry

end QAlgorithms.Papers.Independent.Renew46.P43

end
