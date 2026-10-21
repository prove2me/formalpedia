-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P13_equal_reference_holevo_bound
-- name    : QAlgorithms.Papers.Independent.Claimed50.P13.equal_reference_holevo_bound
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T09:28:33.413978+00:00
-- url     : https://prove2.me/theorems/af2155fa-797c-476c-b07d-322a6ae6f602
-- title:
--   Lemma 1, (16): Holevo bound for equal reference marginals
-- statement:
--   All systems are nonzero separable complex Hilbert spaces. States are positive trace-class operators of trace one, channels are complex-linear completely positive trace-preserving maps on the full trace class, and all logarithms are natural. Write $H$ for von Neumann entropy, $I(\rho,\Phi)$ for the relative-entropy mutual information of a purified input, and $C_\chi$, $C$, $C_{\rm ea}$ for the single-use Holevo, regularized classical and assisted classical capacities, respectively. A second argument $\rho$ in $C_\chi(\Phi,\rho)$ fixes the exact input average. Let $\sigma$ be a reference state on $H_R$, and let $\{p_i,\omega_i\}$ be a finite probability ensemble on $H_A\otimes H_R$ with $(\omega_i)_R=\sigma$ for every $i$. If $\overline\omega=\sum_i p_i\omega_i$, then
--
--   $$\chi_{\Phi\otimes\operatorname{Id}_R}(\{p_i,\omega_i\})\le I(\overline\omega_A,\Phi).$$
--
--   This bounds a finite ensemble output Holevo quantity by the information of its average input when the reference marginal is fixed.
-- source:
--   On the entanglement-assisted classical capacity of infinite-dimensional quantum channels, arXiv:1210.6926v2, PDF p. 9, Lemma 1, (16): Holevo bound for equal reference marginals

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P13

noncomputable section

open MeasureTheory Filter

open scoped ENNReal NNReal Topology BigOperators

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Dependency50.P33

namespace QAlgorithms.Papers.Independent.Claimed50.P13

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Lemma 1, (16), PDF p.9: every ensemble member has reference marginal sigma.
Neither finite entropy nor finite-dimensional output/reference is required. -/
theorem equal_reference_holevo_bound {I J R : Type}
    [Countable I] [Countable J] [Countable R] [Nonempty I] [Nonempty J] [Nonempty R]
    (Phi : MI.Channel I J) (sigma : State R) (m : ℕ) (p : FiniteLaw m)
    (omega : Fin m → State (I × R))
    (hmarginal : ∀ i, MI.traceFirst (omega i).coefficients = sigma.coefficients) :
    finiteHolevo (tensorApply Phi.val) p (fun i => (omega i).coefficients) ≤
      MI.mutualInformation
        (MI.traceSecond (finiteAverage p (fun i => (omega i).coefficients))) Phi.val := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P13

end
