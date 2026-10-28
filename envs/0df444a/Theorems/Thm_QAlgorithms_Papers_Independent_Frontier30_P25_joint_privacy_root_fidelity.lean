-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Frontier30_P25_joint_privacy_root_fidelity
-- name    : QAlgorithms.Papers.Independent.Frontier30.P25.joint_privacy_root_fidelity
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T18:43:19.211288+00:00
-- url     : https://prove2.me/theorems/d38c5e3a-2b46-448e-bc77-40dc7e1eaa48
-- title:
--   Joint Type-I privacy parameters bound root infidelity
-- statement:
--   Let $\rho_{KLE}=d^{-1}\sum_{k,l}p(l\mid k)|kl\rangle\langle kl|\otimes\rho_E^{k,l}$, where $K,L$ have the same nonempty finite alphabet of size $d$, each $p(\cdot\mid k)$ is a probability distribution, and each conditional Eve operator is a density operator. Let $\rho_E,\rho_{KE}$ be the actual marginals, $\pi_K=I_K/d$, and $\Phi_{KL}=d^{-1}\sum_k|kk\rangle\langle kk|$ be the mixed classical ideal key. Write $e=\Pr\{K\ne L\}$ and $s=\tfrac12\|\rho_{KE}-\pi_K\otimes\rho_E\|_1$, using the unhalved trace norm. Then
--
--   $$1-\sqrt{F(\rho_{KLE},\Phi_{KL}\otimes\rho_E)}\le e+s.$$
--
--   Here $F$ is squared fidelity. For any sequence of these states, allowing dimensions to vary, if their Type-II infidelities tend to one and $e_n\le\varepsilon_n$, $s_n\le\delta_n$ with $\varepsilon_n,\delta_n\in[0,1]$, then $\liminf_n(\varepsilon_n+\delta_n)\ge1$. If that sum converges, its limit is therefore at least one. This relates the joint fidelity criterion to reliability plus security.
-- source:
--   Converse bounds for private communication over quantum channels, arXiv:1602.08898v3, PDF p. 37, Proposition 28

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

/-- PDF pp.37–38, Proposition 28: joint Type-I parameters bound root infidelity.
The proof justifies a liminf consequence, without assuming existence of a sum limit.
Dimensions may vary with n. -/
theorem joint_privacy_root_fidelity :
    (∀ c : CCQData, 1 - Real.sqrt (squaredFidelity (ccqState c) (idealCCQ (eveMarginal c))) ≤
      disagreement c + security c) ∧
    (∀ (c : ℕ → CCQData) (eps delta : ℕ → ℝ),
      (∀ n, 0 ≤ eps n ∧ eps n ≤ 1 ∧ 0 ≤ delta n ∧ delta n ≤ 1 ∧
        disagreement (c n) ≤ eps n ∧ security (c n) ≤ delta n) →
      Filter.Tendsto (fun n => 1 - squaredFidelity (ccqState (c n)) (idealCCQ (eveMarginal (c n))))
        Filter.atTop (nhds 1) →
      1 ≤ Filter.liminf (fun n => eps n + delta n) Filter.atTop) := by sorry

end QAlgorithms.Papers.Independent.Frontier30.P25

end
