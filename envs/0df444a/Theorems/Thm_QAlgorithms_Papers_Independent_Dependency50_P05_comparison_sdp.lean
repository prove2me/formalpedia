-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P05_comparison_sdp
-- name    : QAlgorithms.Papers.Independent.Dependency50.P05.comparison_sdp
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T08:03:26.759834+00:00
-- url     : https://prove2.me/theorems/caf3a528-1430-47e6-b300-3a049c6ac46c
-- title:
--   Polynomial-size SDP characterization of channel comparison
-- statement:
--   All systems are finite dimensional complex Hilbert spaces with strictly positive input and output dimensions. A system $A$ comprises $A_0,A_1$. Channels are complex-linear CPTP maps on all operators, and a superchannel is completely CP-preserving and trace-preserving-map preserving. Its complete extension includes both registers of every auxiliary dynamical system. Write $J_\Theta$ for the unnormalized, input-first supermap Choi matrix, $J^S$ for its ordinary partial-trace marginal, and $u^S=I^S/d_S$. Tensor formulas use the named register order. For bipartite channels $\Phi^{RA},\Psi^{RB}$ fix the tomography of Theorem 7 and write $F_{y|x},H_{y|x}$ for the resulting branch Choi matrices. Put $x_0=d_{R_0}^2$, $y_0=d_{R_1}^2$. Minimize, over a test instrument family $K_{y|x}$ and Hermitian $\gamma^{AB_0}$,
--   $$f=\operatorname{Tr}\gamma-\frac1{x_0^2}\sum_{x,y}\operatorname{Tr}(H_{y|x}K_{y|x}),$$
--   subject to $K_{y|x}\ge0$, $\sum_y\operatorname{Tr}_{B_1}K_{y|x}=I^{B_0}$ for each $x$, $\gamma^{A_0B_0}=u^{A_0}\otimes\gamma^{B_0}$, and
--   $$\gamma^{AB_0}\otimes I^{B_1}\ge\frac1{d_{A_0}x_0^2}\sum_{x,y}F_{y|x}\otimes K_{y|x}^{T}.$$
--   The optimum is finite and attained, and $\Psi\prec_q\Phi$ if and only if $f\ge0$. The matrix-variable count is $(d_{A_0}d_{A_1}d_{B_0})^2+x_0y_0(d_{B_0}d_{B_1})^2$; the independent equality count is $(d_{A_0}^2-1)d_{B_0}^2+x_0d_{B_0}^2$, and the total PSD block order is $d_{A_0}d_{A_1}d_{B_0}d_{B_1}+x_0y_0d_{B_0}d_{B_1}$. Each is bounded by $(d_{A_0}+d_{A_1}+d_{B_0}+d_{B_1}+x_0+y_0)^8$. This is a polynomial-size SDP description; no exact finite-precision runtime is asserted.
-- source:
--   Comparison of Quantum Channels by Superchannels, arXiv:1808.02607v3, PDF p. 20, Sec. V-D, Eqs.(99)–(103)

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P05

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

namespace QAlgorithms.Papers.Independent.Dependency50.P05

local notation "Mat" I:max => Matrix I I ℂ

/-- arXiv:1808.02607v3, PDF pp.20–21, Eqs.(99)–(103): exact SDP criterion with polynomial
matrix-variable, equality, and PSD-block counts. The page-20 image prints transpose on Phi.
We use the equivalent test-only transpose after transposing the ENTIRE LMI including gamma;
trace and marginal constraints are invariant under this change of variable.
Independent moderation of the normalization choice is pending. No finite-precision runtime is claimed. -/
theorem comparison_sdp (A B R : System) (F : Mat (ChoiRegister A × ChoiRegister R)) (G : Mat (ChoiRegister B × ChoiRegister R))
    (hF : BipartiteChannel A R F) (hG : BipartiteChannel B R G) (t : Tomography R) :
    (QuantumMajorizes F G ↔ 0 ≤ comparisonSDPValue (extractedBranch F t) (extractedBranch G t)) ∧
    comparisonSDPValue (extractedBranch F t) (extractedBranch G t) ≠ ⊥ ∧
    comparisonSDPValue (extractedBranch F t) (extractedBranch G t) ≠ ⊤ ∧
    (∃ (K : Fin (R.input ^ 2) → Fin (R.output ^ 2) → Mat (ChoiRegister B))
      (H : Mat (ChoiRegister A × In B)), ComparisonFeasible (extractedBranch F t) K H ∧
      comparisonSDPValue (extractedBranch F t) (extractedBranch G t) =
        ((H.trace.re - (1 / (((R.input ^ 2 : ℕ) : ℝ) ^ 2)) *
          ∑ i, ∑ j, (extractedBranch G t i j * K i j).trace.re : ℝ) : EReal)) ∧
    (let x := R.input ^ 2
     let y := R.output ^ 2
     let s := A.input + A.output + B.input + B.output + x + y
     comparisonVariables A B x y ≤ s ^ 8 ∧
       comparisonEqualities A B x ≤ s ^ 8 ∧ comparisonPSDOrder A B x y ≤ s ^ 8) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P05

end
