-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Frontier30_P25_typeII_controls_typeI
-- name    : QAlgorithms.Papers.Independent.Frontier30.P25.typeII_controls_typeI
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T18:44:09.209259+00:00
-- url     : https://prove2.me/theorems/3b0cac94-a29a-406c-8b95-24952571fea7
-- title:
--   Type-II infidelity controls both Type-I privacy parameters
-- statement:
--   For a finite ccq state $\rho_{KLE}=d^{-1}\sum_{k,l}p(l\mid k)|kl\rangle\langle kl|\otimes\rho_E^{k,l}$ with normalized conditional Eve states, nonempty equal key alphabets and uniform $K$, let $\rho_E,\rho_{KE}$ be the actual marginals. Set $\pi_K=I_K/d$ and $\Phi_{KL}=d^{-1}\sum_k|kk\rangle\langle kk|$. Then
--
--   $$\Pr\{K\ne L\}\le\sqrt{1-F(\rho_{KLE},\Phi_{KL}\otimes\rho_E)},\qquad \frac12\|\rho_{KE}-\pi_K\otimes\rho_E\|_1\le\sqrt{1-F(\rho_{KLE},\Phi_{KL}\otimes\rho_E)}.$$
--
--   The fidelity is squared and the trace norm is unhalved. Consequently, if $F=1-\eta$ with $0\le\eta\le1$, both Type-I parameters are at most $\sqrt\eta$. This transfers a Type-II guarantee to separate reliability and security guarantees.
-- source:
--   Converse bounds for private communication over quantum channels, arXiv:1602.08898v3, PDF p. 38, Proposition 29

import Definitions.Def_QAlgorithms_Papers_Independent_Frontier30_P25

noncomputable section

namespace QAlgorithms.Papers.Independent.Frontier30.P25

open scoped Matrix ComplexConjugate ENNReal

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

-- Pinned accepted definitions; assessments record the domains of equivalence.

open QAlgorithms.Papers.Independent.Dependency50.P09 (OneDesign relativeD sandwichedD)

open QAlgorithms.Papers.Independent.Dependency50.P24 (logBits idealCCQ)

open QAlgorithms.Papers.Independent.Information100.P22 (bell)

open QAlgorithms.Papers.Independent.Information100.P58 (testingD)

open QAlgorithms.Papers.Independent.Information100.P67 (squaredFidelity privateState privacyTest)

/-- PDF pp.38–39, Proposition 29: both Type-I parameters are bounded by sqrt(1-F).
The security parameter is half the unhalved trace norm. -/
theorem typeII_controls_typeI (c : CCQData) :
    (disagreement c ≤ Real.sqrt (1 - squaredFidelity (ccqState c) (idealCCQ (eveMarginal c))) ∧
      security c ≤ Real.sqrt (1 - squaredFidelity (ccqState c) (idealCCQ (eveMarginal c)))) ∧
    (∀ eta : ℝ, 0 ≤ eta → eta ≤ 1 → squaredFidelity (ccqState c) (idealCCQ (eveMarginal c)) = 1 - eta →
      disagreement c ≤ Real.sqrt eta ∧ security c ≤ Real.sqrt eta) := by sorry

end QAlgorithms.Papers.Independent.Frontier30.P25

end
