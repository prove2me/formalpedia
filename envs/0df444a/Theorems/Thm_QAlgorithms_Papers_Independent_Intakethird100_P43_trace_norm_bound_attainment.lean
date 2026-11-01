-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P43_trace_norm_bound_attainment
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P43.trace_norm_bound_attainment
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T05:22:23.508561+00:00
-- url     : https://prove2.me/theorems/db5c8663-2e28-49ed-adbf-54490a8a888e
-- title:
--   Sufficient condition for attaining the trace-norm fidelity bound
-- statement:
--   All operators act on a finite bipartite space $\mathbb C^d\otimes\mathbb C^d$ in a fixed product basis. Write $\Gamma=T_2$ for Bob's partial transpose and $P_m=|\psi_m\rangle\langle\psi_m|$, where $|\psi_m\rangle=m^{-1/2}\sum_i|ii\rangle$. A density operator is positive semidefinite with complex trace exactly one. An admissible PPT map is complex-linear, positive and trace preserving, and $\Gamma_{\rm out}T\Gamma_{\rm in}$ is positive on every positive operator. A PPT channel is additionally completely positive; complete positivity of the transpose-conjugated map is not required. Fidelity means the overlap $\operatorname{tr}(P_m T(\rho))$.
--
--   Let $d\ge1$, $m\ge2$, and let $\rho$ be any density operator. Let $P_{\rm neg}$ be the negative spectral projector of $\rho^\Gamma$. If $\|P_{\rm neg}^\Gamma\|_\infty\le1/2$, then $A=(I-2P_{\rm neg}^\Gamma)/m$ is admissible and its isotropic PPT channel attains the optimal overlap:
--
--   $$\operatorname{tr}(P_mT_A(\rho))=F_m(\rho)=\frac{\|\rho^\Gamma\|_1}{m}.$$
--
--   The optimum is over admissible positive PPT maps. This is a sufficient condition only and includes PPT states, for which $P_{\rm neg}=0$ and $A=I/m$.
-- source:
--   Distillability via protocols respecting the positivity of partial transpose, arXiv:quant-ph/0104095v2, PDF p. 3, Sentence immediately after Eq. (10)

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P43

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

namespace QAlgorithms.Papers.Independent.Intakethird100.P43

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P04
  (gamma copies bellProjector negativeProjector werner)

open QAlgorithms.Papers.Independent.Information100.P30 (IsPositiveMap)

/-- PDF p.3, last sentence before Section III: sufficient condition for attaining
(10), with the explicit epsilon=2 channel. Includes PPT states, where P_neg=0.
The nontrivial target restriction m>=2 is inherited from (6); no converse is asserted. -/
theorem trace_norm_bound_attainment (d m : ℕ) (hd : 0 < d) (hm : 2 ≤ m)
    (rho : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)
    (hrho : IsDensityMatrix rho)
    (hsmall : specNorm (gamma (negativeProjector rho)) ≤ 1/2) :
    let A := negativeSpaceWitness rho m 2
    RainsFeasibleEffect m A ∧ IsPositiveConjugatePPTChannel (isotropicPreparation m A) ∧
      effectProb (bellProjector m) (isotropicPreparation m A rho) = traceNorm (gamma rho) / (m : ℝ) ∧
      IsGreatest (positivePPTFidelityValues rho m) (traceNorm (gamma rho) / (m : ℝ)) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P43

end
