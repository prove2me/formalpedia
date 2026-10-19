-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P22_jointSignalTomography
-- name    : QAlgorithms.Papers.Independent.Information100.P22.jointSignalTomography
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T10:12:45.327293+00:00
-- url     : https://prove2.me/theorems/2b4a1d72-9175-4f9f-96f9-4732eda13460
-- title:
--   Eqs.(S56)–(S57), unnumbered: complete joint-signal Bloch statistics
-- statement:
--   For the fixed three-signal rank-two graph and YZ encoder, let the input qubit be $\rho=(I+r_xX+r_yY+r_zZ)/2$. Whenever this is a density operator,
--   $$C_S(\rho)=\tfrac18[I-r_xX^{\otimes3}-r_zY^{\otimes3}+r_yZ^{\otimes3}].$$
--   Thus $\operatorname{Tr}(X^{\otimes3}C_S)=-r_x$, $\operatorname{Tr}(Y^{\otimes3}C_S)=-r_z$ and $\operatorname{Tr}(Z^{\otimes3}C_S)=r_y$. The complete signal channel is injective on density operators, while each individual signal remains uniformly concealed. This is statistical state identification and asserts no CPTP inverse from signals alone.
-- source:
--   Beyond Maximal Entanglement : Exact Resources for Multiparty Encrypted Quantum Cloning, arXiv:2609.28241v1, PDF p. 39, Eqs.(S56)–(S57), unnumbered: complete joint-signal Bloch statistics

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P22

namespace QAlgorithms.Papers.Independent.Information100.P22

open scoped ComplexConjugate ComplexOrder Matrix

noncomputable section

local instance (p : Prop) : Decidable p := Classical.propDecidable p

local instance {I : Type*} [Fintype I] [DecidableEq I] (G : CutGraph I) :
    Fintype (cutKernel G) := Fintype.ofFinite _

/-- Eqs.(S56)–(S57), PDF pp.39–40: signs and y/z interchange retained; injectivity of states. -/
theorem jointSignalTomography :
    (∀ (rx ry rz : ℝ), let rho : Op (Qubits 1) :=
      fun a b => (((1/2 : ℂ) • (1 + (rx : ℂ) • pauliX + (ry : ℂ) • pauliY +
        (rz : ℂ) • pauliZ)) : Op Bool) (a 0) (b 0)
      IsDensityMatrix rho → jointSignals (graphVector rankTwoExample) (twoPauliEncoder 3 1 .Y .Z) rho =
        (1/8 : ℂ) • (1 - (rx : ℂ) • tensorOps (fun _ : Wires 3 1 => pauliX) -
          (rz : ℂ) • tensorOps (fun _ : Wires 3 1 => pauliY) +
          (ry : ℂ) • tensorOps (fun _ : Wires 3 1 => pauliZ))) ∧
    (∀ rho sigma : Op (Qubits 1), IsDensityMatrix rho → IsDensityMatrix sigma →
      jointSignals (graphVector rankTwoExample) (twoPauliEncoder 3 1 .Y .Z) rho =
        jointSignals (graphVector rankTwoExample) (twoPauliEncoder 3 1 .Y .Z) sigma → rho = sigma) ∧
    UniformlyConcealed (graphVector rankTwoExample) (twoPauliEncoder 3 1 .Y .Z) := by sorry

end

end QAlgorithms.Papers.Independent.Information100.P22
