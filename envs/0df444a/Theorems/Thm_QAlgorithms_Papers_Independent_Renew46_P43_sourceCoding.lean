-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P43_sourceCoding
-- name    : QAlgorithms.Papers.Independent.Renew46.P43.sourceCoding
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-22T06:21:09.48342+00:00
-- url     : https://prove2.me/theorems/c941238d-6a98-4f69-8715-299fabb61555
-- title:
--   Theorem I.7: For every 0<lambda<1, Rq,Fe(lambda)=Rq,Fbar(lambda)=Ra,Fbar(lambda)=H(averageState).
-- statement:
--   Let a finite pure-state iid source have average $\bar\rho$ on a nonzero finite system of Hilbert dimension $d$. Compression spaces and block lengths are positive, decoders are CPTP and all entropies/rates are in bits. The fixed-error rates are limsups of the actual block minimum of $\log_2\dim\mathcal K/n$. Quantum encoding requires a CPTP extension; arbitrary encoding is state valued. In finite-block bounds $\alpha>0$, $K_V=2\log_2(e)/e$, and $N,\mu$ are the support rank and least positive eigenvalue of $\sqrt{\bar\rho(1-\bar\rho)}$. The Schumacher code compresses onto the nonzero variance-typical range and decodes by inclusion; the strong converse permits any arbitrary-encoding code of fidelity error at most $\lambda$. For the intrinsic version the source letters and decoder lie in the specified classical, hybrid or full matrix algebra, with its intrinsic trace.
--
--   $$
--   R_{q,F_e}(\lambda)=R_{q,\bar F}(\lambda)=R_{a,\bar F}(\lambda)=H(\bar\rho),\qquad 0<\lambda<1.
--   $$
--
--   This is the source result with its stated operational or information-theoretic domain.
-- source:
--   Coding Theorems of Quantum Information Theory, arXiv:quant-ph/9907077v1, PDF p. 11, Theorem I.7

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

/-- Theorem I.7, PDF p.11: all three fixed-error limsup rates, not just the
vanishing-error capacity, equal the ensemble's entropy. -/
theorem sourceCoding {a d : ℕ} (S : PureSource a d) (lambda : ℝ)
    (hlambda : 0 < lambda) (hsmall : lambda < 1) :
    sourceRate S .quantumEntanglement lambda = ENNReal.ofReal (vnEntropy S.average) ∧
    sourceRate S .quantumFidelity lambda = ENNReal.ofReal (vnEntropy S.average) ∧
    sourceRate S .arbitraryFidelity lambda = ENNReal.ofReal (vnEntropy S.average) := by sorry

end QAlgorithms.Papers.Independent.Renew46.P43

end
