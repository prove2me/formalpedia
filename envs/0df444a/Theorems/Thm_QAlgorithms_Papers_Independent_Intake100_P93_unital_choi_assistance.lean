-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P93_unital_choi_assistance
-- name    : QAlgorithms.Papers.Independent.Intake100.P93.unital_choi_assistance
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T11:46:00.959172+00:00
-- url     : https://prove2.me/theorems/098dd5df-ebaf-4463-9e66-f2af39e85ada
-- title:
--   §VII: assistance of a unital channel Choi state
-- statement:
--   Let $T$ be a trace-preserving completely positive map on a nonzero $d$-dimensional system, with $T(I)=I$. Let $\Phi_d=d^{-1/2}\sum_i|ii\rangle$ and $\rho_T=(\mathrm{id}\otimes T)(|\Phi_d\rangle\langle\Phi_d|)$ be its normalized Choi state. Its operational asymptotic assistance is
--
--   $$E_A^\infty(\rho_T)=\log_2d.$$
--
--   The helper holds a purification of $\rho_T$, and the distillation model is finite-dimensional LOCC on i.i.d. copies with vanishing joint error. For $d=1$, the rate is zero. This is an entropy/yield statement, without a channel-norm or componentwise fidelity conclusion.
-- source:
--   Entanglement of assistance and multipartite state distillation, arXiv:quant-ph/0505038v1, PDF p. 8, §VII: assistance of a unital channel Choi state

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P93

namespace QAlgorithms.Papers.Independent.Intake100.P93

open scoped Matrix ComplexConjugate ComplexOrder

noncomputable section

attribute [local instance] Classical.propDecidable Classical.decEq

-- Exact accepted primitives; no chunk-local aliases.

open Information100.P21 (Op)

open Information100.P08 (PureEnsemble)

open Dependency50.P07 (bipartiteProduct)

open Information100.P67 (receiverChannel)

open Support50.P11 (choiState)

/-- PDF p.8, Section VII: entropy assistance of the normalized unital channel
state. The positive-dimensional singleton case has rate log2(1)=0. -/
theorem unital_choi_assistance {d : ℕ} (hd : 0 < d)
    (T : Superop (Fin d) (Fin d)) (hT : IsChannel T) (hu : T 1 = 1) :
    operationalAssistance (choiState T) = Real.logb 2 d := by sorry

end

end QAlgorithms.Papers.Independent.Intake100.P93
