-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P43_intrinsicSourceCoding
-- name    : QAlgorithms.Papers.Independent.Renew46.P43.intrinsicSourceCoding
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-22T06:31:30.414197+00:00
-- url     : https://prove2.me/theorems/b02c278e-18e4-4204-a046-4e1eae68db6e
-- title:
--   Theorem I.22: For pure-state source on any finite intrinsic C*-algebra and 0<lambda<1: Rq,Fbar(lambda)=Ra,Fbar(lambda)=H(averageState).
-- statement:
--   Let a finite pure-state iid source have average $\bar\rho$ on a nonzero finite system of Hilbert dimension $d$. Compression spaces and block lengths are positive, decoders are CPTP and all entropies/rates are in bits. The fixed-error rates are limsups of the actual block minimum of $\log_2\dim\mathcal K/n$. Quantum encoding requires a CPTP extension; arbitrary encoding is state valued. In finite-block bounds $\alpha>0$, $K_V=2\log_2(e)/e$, and $N,\mu$ are the support rank and least positive eigenvalue of $\sqrt{\bar\rho(1-\bar\rho)}$. The Schumacher code compresses onto the nonzero variance-typical range and decodes by inclusion; the strong converse permits any arbitrary-encoding code of fidelity error at most $\lambda$. For the intrinsic version the source letters and decoder lie in the specified classical, hybrid or full matrix algebra, with its intrinsic trace.
--
--   $$
--   R_{q,\bar F}(\lambda)=R_{a,\bar F}(\lambda)=H(\bar\rho),\qquad0<\lambda<1.
--   $$
--
--   This is the source result with its stated operational or information-theoretic domain.
-- source:
--   Coding Theorems of Quantum Information Theory, arXiv:quant-ph/9907077v1, PDF p. 20, Theorem I.22

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

open QAlgorithms.Papers.Independent.Claimed50.P40 (InBlocks)

attribute [local instance] QAlgorithms.Papers.Independent.Renew46.P43.matrixMeasurableSpace

/-- Theorem I.22, PDF p.20: classical, hybrid and fully quantum intrinsic sources.
No entanglement-fidelity assertion is made outside the full matrix setting. -/
theorem intrinsicSourceCoding {a : ℕ} (A : IntrinsicSystem) (S : PureSource a A.dim)
    (hletters : ∀ x, InBlocks A.block (S.letter x))
    (lambda : ℝ) (hlambda : 0 < lambda) (hsmall : lambda < 1) :
    intrinsicSourceRate A S true lambda = ENNReal.ofReal (vnEntropy S.average) ∧
    intrinsicSourceRate A S false lambda = ENNReal.ofReal (vnEntropy S.average) := by sorry

end QAlgorithms.Papers.Independent.Renew46.P43

end
