-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P48_independent_instrument
-- name    : QAlgorithms.Papers.Independent.Information100.P48.independent_instrument
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T11:41:29.803986+00:00
-- url     : https://prove2.me/theorems/12d64ecc-b356-4a8c-82c8-53eb2da71605
-- title:
--   Independent-environment coherent-control instrument
-- statement:
--   Let $E_0,E_1$ be finite environmental registers with designated initial pure basis states $|e_0\rangle,|e_1\rangle$, and let $\rho$ be any qubit density matrix. Fix unitaries $U_i$ on $S\otimes E_i$, embedded with identity on the inactive environment. Put $D_i=\operatorname{Tr}_{E_i}[U_i(\rho\otimes|e_i\rangle\langle e_i|)U_i^\dagger]$ and $T_i=\langle e_i|U_i|e_i\rangle$. With initial control $|+\rangle$, the reduced control/system blocks are $\frac12\begin{pmatrix}D_0&T_0\rho T_1^\dagger\\T_1\rho T_0^\dagger&D_1\end{pmatrix}$. Measuring the control in its Hadamard basis produces CP outcome maps
--
--   $$
--   \Phi_\pm(\rho)=\frac{D_0+D_1}{4}\ \pm\ \frac{T_0\rho T_1^\dagger+T_1\rho T_0^\dagger}{4}.
--   $$
--
--   These equal the maps obtained from the joint selected operators $(\widehat U_0\pm\widehat U_1)/2$ followed by environmental trace. Their probabilities $p_\pm=\operatorname{Tr}\Phi_\pm(\rho)$ lie in $[0,1]$ and sum to one; if $p_\pm>0$, $\Phi_\pm(\rho)/p_\pm$ is a density matrix. If $D_0=D_1=D$ and $T_0=T_1=T$, the formula simplifies to $D/2\pm T\rho T^\dagger/2$. Initial control $|-\rangle$ swaps the selected labels. This retains the physical instrument rather than only a scalar interference value.
-- source:
--   Coherent Control of Channel Dilations Activate Temporal Bell Nonclassicality, arXiv:2607.05643v1, PDF p. 4, §III A, Eqs.(14)–(29): independent-environment instrument and interference

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P48

namespace QAlgorithms.Papers.Independent.Information100.P48

open scoped Matrix ComplexConjugate

noncomputable section

/-- §III A, PDF pp.4–5, Eqs.(14)–(29): independent-environment instrument,
including joint blocks, interference, both probabilities and positive-trace normalization.
An initial minus control swaps the outcome labels. -/
theorem independent_instrument
    {E0 E1 : Type*} [Fintype E0] [Fintype E1] [DecidableEq E0] [DecidableEq E1]
    (e0 : E0) (e1 : E1)
    (U0 : Matrix.unitaryGroup (Bool × E0) ℂ)
    (U1 : Matrix.unitaryGroup (Bool × E1) ℂ)
    (rho : QOp) (hrho : IsDensityMatrix rho) :
    let U := embed0 (E1 := E1) (U0 : Matrix (Bool × E0) (Bool × E0) ℂ)
    let V := embed1 (E0 := E0) (U1 : Matrix (Bool × E1) (Bool × E1) ℂ)
    let D0 := cross (U0 : Matrix (Bool × E0) (Bool × E0) ℂ) U0 e0 rho
    let D1 := cross (U1 : Matrix (Bool × E1) (Bool × E1) ℂ) U1 e1 rho
    let T0 := interference (U0 : Matrix (Bool × E0) (Bool × E0) ℂ) e0
    let T1 := interference (U1 : Matrix (Bool × E1) (Bool × E1) ℂ) e1
    jointCS (hadamardProjector false) U V (e0, e1) rho =
      controlBlocks D0 D1 (T0 * rho * T1ᴴ) (T1 * rho * T0ᴴ) ∧
    (∀ minus : Bool,
      selectControl (jointCS (hadamardProjector false) U V (e0, e1) rho) minus =
        branch U V (e0, e1) minus rho ∧
      branch U V (e0, e1) minus rho = (1 / 4 : ℂ) • (D0 + D1) +
        ((outcomeSign minus / 4 : ℝ) : ℂ) • (T0 * rho * T1ᴴ + T1 * rho * T0ᴴ) ∧
      IsCP (branch U V (e0, e1) minus) ∧
      0 ≤ (branch U V (e0, e1) minus rho).trace.re ∧
      (branch U V (e0, e1) minus rho).trace.re ≤ 1 ∧
      (0 < (branch U V (e0, e1) minus rho).trace.re →
        IsDensityMatrix (normalize (branch U V (e0, e1) minus rho)))) ∧
    (branch U V (e0, e1) false rho).trace.re +
      (branch U V (e0, e1) true rho).trace.re = 1 ∧
    (∀ minus : Bool, D0 = D1 → T0 = T1 →
      branch U V (e0, e1) minus rho = (1 / 2 : ℂ) • D0 +
        ((outcomeSign minus / 2 : ℝ) : ℂ) • (T0 * rho * T0ᴴ)) ∧
    (∀ minus : Bool,
      selectControl (jointCS (hadamardProjector true) U V (e0, e1) rho) minus =
        branch U V (e0, e1) (!minus) rho) := by sorry

end

end QAlgorithms.Papers.Independent.Information100.P48
