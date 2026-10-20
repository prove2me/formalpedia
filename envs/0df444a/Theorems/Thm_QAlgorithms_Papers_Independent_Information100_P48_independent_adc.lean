-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P48_independent_adc
-- name    : QAlgorithms.Papers.Independent.Information100.P48.independent_adc
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T11:42:03.251108+00:00
-- url     : https://prove2.me/theorems/e0b721bb-320d-4d9d-ad6d-caef96ed70f7
-- title:
--   Both independent-environment ADC coherent outcome maps
-- statement:
--   Fix $\gamma\in[0,1]$ and two identical principal-angle ADC dilations acting on independent environmental qubits initially in $|00\rangle$. Prepare the control in $|+\rangle$ and measure it in the Hadamard basis. The clean interference operator is $T=K_0$. On every qubit input operator $R$, the actual outcome maps are
--
--   $$
--   \Phi^{\rm ind}_+(R)=K_0RK_0^\dagger+\tfrac12K_1RK_1^\dagger,\qquad
--   \Phi^{\rm ind}_-(R)=\tfrac12K_1RK_1^\dagger.
--   $$
--
--   For any density input $\rho$, writing $\rho_{11}=\langle1|\rho|1\rangle$, their success probabilities are $p_+=1-\gamma\rho_{11}/2$ and $p_-=\gamma\rho_{11}/2$. Every positive-probability branch normalizes to a density matrix. For initial system state $I/2$, sequential projectors $M_a,M_b$ give raw joint probability $\frac12\operatorname{Tr}[M_b\Phi^{\rm ind}_\pm(M_a)]$. This displays the operational mixture underlying the independent-control activation curve.
-- source:
--   Coherent Control of Channel Dilations Activate Temporal Bell Nonclassicality, arXiv:2607.05643v1, PDF p. 5, §III A, Eqs.(26)–(31): ADC independent-control outcome maps

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P48

namespace QAlgorithms.Papers.Independent.Information100.P48

open scoped Matrix ComplexConjugate

noncomputable section

/-- §III A, PDF pp.5–6, Eqs.(26)–(31): actual ADC independent-control outcome maps.
The minus branch is retained even when its probability is zero. -/
theorem independent_adc (g : ℝ) (hg0 : 0 ≤ g) (hg1 : g ≤ 1) :
    interference (dilation g) false = k0 g ∧
    (∀ rho : QOp,
      independentADC g false rho = k0 g * rho * (k0 g)ᴴ +
        (1 / 2 : ℂ) • (k1 g * rho * (k1 g)ᴴ) ∧
      independentADC g true rho = (1 / 2 : ℂ) • (k1 g * rho * (k1 g)ᴴ)) ∧
    (∀ rho : QOp, IsDensityMatrix rho → ∀ minus : Bool,
      (independentADC g minus rho).trace.re =
        (if minus then g / 2 * (rho true true).re else 1 - g / 2 * (rho true true).re) ∧
      (0 < (independentADC g minus rho).trace.re →
        IsDensityMatrix (normalize (independentADC g minus rho)))) ∧
    (∀ (A B : QOp) (a b minus : Bool),
      rawJoint (independentADC g minus) A B a b =
        (1 / 2 : ℝ) * (projector B b * independentADC g minus (projector A a)).trace.re) := by sorry

end

end QAlgorithms.Papers.Independent.Information100.P48
