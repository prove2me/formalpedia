-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P08_concurrenceFactorization
-- name    : QAlgorithms.Papers.Independent.Information100.P08.concurrenceFactorization
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T16:17:34.450977+00:00
-- url     : https://prove2.me/theorems/2dbdf772-1d03-4613-866b-eafef95c6180
-- title:
--   Appendix A: qubit concurrence factorization
-- statement:
--   All systems below have finite positive dimension. States are positive semidefinite matrices of trace one, channels are completely positive trace-preserving maps, and entropies are in bits. Write $S$ for von Neumann entropy and $E_F(A;B)$ for the pure convex roof of marginal entropy across the indicated cut. Let $\mathcal N$ be any qubit channel, $\rho$ any qubit density matrix, and $\phi^\rho$ its canonical purification with transmitted marginal $\rho$. Let $\theta_{\mathcal N}$ be the normalized Choi state. Define pure concurrence by $c(v)=2|\det C_v|$, where $C_v$ is the two-qubit coefficient matrix, and mixed concurrence by its pure convex roof. Then $$c((\mathrm{id}\otimes\mathcal N)(\phi^\rho))=2\sqrt{\det\rho}\,c(\theta_{\mathcal N}).$$ Singular inputs are included. This is the local-filter factorization derived with attribution in Appendix A.
-- source:
--   Entanglement -of-formation potentials for feedback-assisted classical communication and randomness distillation, arXiv:2610.04831v1, PDF p. 66, Appendix A: qubit concurrence factorization

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P08

namespace QAlgorithms.Papers.Independent.Information100.P08

open scoped Matrix ComplexConjugate ComplexOrder

noncomputable section

attribute [local instance] Classical.propDecidable

/-- PDF p.66, (A.2): concurrence factorization, including singular input density matrices. -/
theorem concurrenceFactorization (N : Superop (Fin 2) (Fin 2)) (hN : IsChannel N)
    (rho : Matrix (Fin 2) (Fin 2) ℂ) (hrho : IsDensityMatrix rho) :
    concurrence (idTensorSuperop N (pureDensity (canonicalPurification rho))) =
      2 * Real.sqrt rho.det.re * concurrence (choi N) := by sorry

end

end QAlgorithms.Papers.Independent.Information100.P08
