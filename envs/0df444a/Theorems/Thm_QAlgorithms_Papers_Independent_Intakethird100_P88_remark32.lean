-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P88_remark32
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P88.remark32
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T04:16:28.380746+00:00
-- url     : https://prove2.me/theorems/ba4588b1-fe28-4d39-9543-7c3e91074eeb
-- title:
--   Zero second argument in the linearized variational programs
-- statement:
--   Let $\rho$ be any positive trace-class operator of trace one on a complex Hilbert space. In the three linearized variational programs of Lemma 20, set the second operator to zero. They remain well defined and satisfy
--
--   $$
--   \begin{aligned}
--   D_M(\rho\|0)
--   &=\sup_{h\in\mathcal B_{\mathrm{sa}}}\{\operatorname{Tr}(\rho h)+\log_2 e\}\\
--   &=\sup_{L\in\mathcal B_{\mathrm{sa}},\,L\ge\delta I,\,\delta>0}\{\operatorname{Tr}(\rho\log_2L)+\log_2 e\}\\
--   &=\sup_{L\in\mathcal B_{\mathrm{sa}},\,L>0}\{\operatorname{Tr}(\rho\log_2L)+\log_2 e\}=+\infty.
--   \end{aligned}
--   $$
--
--   The middle domain requires some positive lower spectral bound, depending on $L$. This records the zero-input extension of precisely the linearized programs (24), (26), and (28).
-- source:
--   Asymptotic state transformations of continuous variable resources, arXiv:2010.00044v3, PDF p. 20, VII A: Remark32

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P88

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakethird100.P88

open Filter

open QAlgorithms.Papers.Independent.Dependency50.P13

open QAlgorithms.Papers.Independent.Dependency50.P39 (Fock fockKet fockDyad)

open QAlgorithms.Papers.Independent.Information100.P62 (logTwo)

attribute [local instance] Classical.propDecidable

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- PDF p.20, Remark 32: only the three linearized programs extend to sigma=0.
All equal the actual measured relative entropy, namely plus infinity.
Source correction in its measured-entropy dependency: printed (10), p.5,
repeats P_rho; changed its second distribution to P_sigma, as the pp.19-20
proof requires. This also makes the sigma=0 conclusion meaningful. -/
theorem remark32 {I : Type*} (b : HilbertBasis I ℂ H) (rho : State b) :
    traceClassMeasuredEntropyBits b rho zeroPositive = ⊤ ∧
    exponentialProgram b rho zeroPositive true = ⊤ ∧
    positiveProgram b rho zeroPositive true true = ⊤ ∧
    positiveProgram b rho zeroPositive false true = ⊤ := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P88

end
