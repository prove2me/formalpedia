-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P48_dilationChoice_strictlyEnlarges
-- name    : QAlgorithms.Papers.Independent.Information100.P48.dilationChoice_strictlyEnlarges
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T11:39:33.973051+00:00
-- url     : https://prove2.me/theorems/597f4ee5-e784-425a-b4a6-07337b726f88
-- title:
--   Dilation choice strictly enlarges equatorial temporal-CHSH activation
-- statement:
--   Consider a system qubit initially in $I/2$, amplitude damping of strength $\gamma\in[0,1]$, and the fixed settings $A_1=X$, $A_2=Y$, $B_1=(X+Y)/\sqrt2$, $B_2=(X-Y)/\sqrt2$. Prepare a separate control in $|+\rangle$, select its Hadamard $+$ outcome, and normalize the sequential probabilities by the actual success probability. Write $\Phi^{\rm ind}_{\gamma,\pm}$ for the outcome maps from two identical principal-angle dilations on independent clean environments and $\Phi^D_{\gamma,\pm}$ for forward/inverse dilations on one clean environment. Define activation as violation when the deterministic ADC does not violate. Then
--
--   $$
--   \mathcal A_{\rm ind}=[1/2,4\sqrt{10}-12),\qquad
--   \mathcal A_D=[1/2,2(\sqrt2-1)),\qquad
--   \mathcal A_{\rm ind}\subsetneq\mathcal A_D.
--   $$
--
--   Both instruments sum to the same deterministic ADC on every input operator. Nevertheless, at $\gamma=1/2$ their normalized selected outputs differ for some density input. This establishes operational dependence on the physical dilation without optimizing over every possible dilation.
-- source:
--   Coherent Control of Channel Dilations Activate Temporal Bell Nonclassicality, arXiv:2607.05643v1, PDF p. 1, Abstract / §§IV–V: dilation choice strictly enlarges equatorial temporal-CHSH activation

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P48

namespace QAlgorithms.Papers.Independent.Information100.P48

open scoped Matrix ComplexConjugate

noncomputable section

/-- Abstract and §§IV–V, PDF pp.1,8–10: identical deterministic maps but strictly
larger fixed-equatorial activation for shared forward/inverse dilation control.
No optimality over arbitrary dilations or filters is asserted. -/
theorem dilationChoice_strictlyEnlarges :
    activation (fun g => independentADC g false) = Set.Ico (1 / 2) independentCritical ∧
    activation (fun g => sharedADC g false) = Set.Ico (1 / 2) sharedCritical ∧
    activation (fun g => independentADC g false) ⊂
      activation (fun g => sharedADC g false) ∧
    (∀ g : ℝ, 0 ≤ g → g ≤ 1 → ∀ rho : QOp,
      independentADC g false rho + independentADC g true rho = adc g rho ∧
      sharedADC g false rho + sharedADC g true rho = adc g rho) ∧
    (∃ rho : QOp, IsDensityMatrix rho ∧
      normalize (independentADC (1 / 2) false rho) ≠
        normalize (sharedADC (1 / 2) false rho)) := by sorry

end

end QAlgorithms.Papers.Independent.Information100.P48
