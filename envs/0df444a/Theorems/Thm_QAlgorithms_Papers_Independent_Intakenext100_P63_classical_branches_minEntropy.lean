-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P63_classical_branches_minEntropy
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P63.classical_branches_minEntropy
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T07:17:34.929189+00:00
-- url     : https://prove2.me/theorems/40dfccb2-729d-428b-9316-c71e3c57b6c8
-- title:
--   Conditional min-entropy bounds from classical branches
-- statement:
--   Let $A$ be a nonzero finite-dimensional space and let $J$ be finite and nonempty. Take a probability vector $(q_j)$ and normalized densities $\rho_j^A$ for every label, including zero-weight labels. Set $\rho^{AJ}=\sum_jq_j\rho_j^A\otimes|j\rangle\langle j|$. For $\varepsilon\ge0$, $0\le\delta<1$, and a set $T\subseteq J$ satisfying $\sum_{j\notin T}q_j\le\delta$,
--
--   $$H_{\min}(A|J)_\rho\ge\min_jH_{\min}(\rho_j),\qquad H_{\min}^{\varepsilon+\delta}(A|J)_\rho\ge\min_{j\in T}H_{\min}^{\varepsilon}(\rho_j).$$
--
--   Smoothing always ranges over normalized states within half trace-norm distance of the original state, and conditional min-entropy optimizes a normalized reference density. The retained set has positive probability and is nonempty. Radii at least one remain defined. These bounds pass uncertainty on individual retained branches to a classical conditioning register.
-- source:
--   Weak locking capacity of quantum channels can be much larger than private capacity, arXiv:1403.6361v3, PDF p. 9, Remark 8: conditional min-entropy bounds from classical branches

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P63

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakenext100.P63

open QAlgorithms Filter

open QAlgorithms.Papers.Independent.Information100.P63 (Mat)

open QAlgorithms.Papers.Independent.Information100.P04 (Measurement)

open QAlgorithms.Papers.Independent.Information100.P27 (shannon labelInformation)

open QAlgorithms.Papers.Independent.Information100.P71 (channelPower dilationMap SupportIncluded)

open QAlgorithms.Papers.Independent.Bridge50.P47 (SymmetricIndex universalSymmetricDilation)

open QAlgorithms.Learning (IsDistribution)

open scoped Matrix ComplexConjugate ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF p.9, Remark 8: normalized classical branches, including zero-weight labels.
Smoothing uses half trace norm; the retained set has positive probability. -/
theorem classical_branches_minEntropy {A J : Type}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype J] [DecidableEq J] [Nonempty J]
    (q : J → ℝ) (hq : IsDistribution q) (rho : J → Mat A)
    (hrho : ∀ j, IsDensityMatrix (rho j)) (eps delta : ℝ)
    (he : 0 ≤ eps) (hd0 : 0 ≤ delta) (hd1 : delta < 1)
    (T : Finset J) (hT : ∑ j ∈ Tᶜ, q j ≤ delta) :
    (sInf (Set.range (fun j => stateMinBits (rho j))) ≤ conditionalMinBits (qcBranchDensity q rho)) ∧
    (sInf {h | ∃ j ∈ T, h = traceSmoothStateMinBits eps (rho j)} ≤
      traceSmoothConditionalMinBits (eps + delta) (qcBranchDensity q rho)) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P63

end
