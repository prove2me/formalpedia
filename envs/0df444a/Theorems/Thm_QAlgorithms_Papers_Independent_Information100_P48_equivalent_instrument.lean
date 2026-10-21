-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P48_equivalent_instrument
-- name    : QAlgorithms.Papers.Independent.Information100.P48.equivalent_instrument
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T11:42:45.929711+00:00
-- url     : https://prove2.me/theorems/e30b9c18-5bbb-487e-9f16-b1a3facdfccc
-- title:
--   Shared-environment instrument and linear cross maps
-- statement:
--   Let $E$ be a finite environment with initial pure basis state $|e\rangle$, let $\rho$ be a qubit density matrix, and fix unitaries $U_0$ on $S\otimes E$ and $V$ on $E$. Define $U_1=(I\otimes V)U_0$ and $\Gamma_{ij}(R)=\operatorname{Tr}_E[U_i(R\otimes|e\rangle\langle e|)U_j^\dagger]$. The diagonal maps agree on every operator; write their common value at $\rho$ as $D$. Both cross maps are complex-linear. With initial control $|+\rangle$, the reduced control/system blocks are $\frac12\begin{pmatrix}D&\Gamma_{01}(\rho)\\\Gamma_{10}(\rho)&D\end{pmatrix}$ and the Hadamard outcome maps satisfy
--
--   $$
--   \Phi_\pm(\rho)=\frac12D\ \pm\ \frac14\bigl(\Gamma_{01}(\rho)+\Gamma_{10}(\rho)\bigr).
--   $$
--
--   These are the CP maps obtained by selecting joint operators $(U_0\pm U_1)/2$. Their trace probabilities lie in $[0,1]$ and sum to one, and positive-trace outputs normalize to density matrices. The cross maps need not be channels: $U_0=I$, $U_1=-I$ on qubit system/environment gives $\Gamma_{01}(R)=-R$. This separates the physical CP outcomes from their generally non-CPTP interference terms.
-- source:
--   Coherent Control of Channel Dilations Activate Temporal Bell Nonclassicality, arXiv:2607.05643v1, PDF p. 6, §III B, Eqs.(32)–(49): shared-environment dilation control and cross maps

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P48

namespace QAlgorithms.Papers.Independent.Information100.P48

open scoped Matrix ComplexConjugate

noncomputable section

/-- §III B, PDF pp.6–8, Eqs.(32)–(49): environment-unitary related dilations.
Equality of the reduced channels is a conclusion. Cross maps are linear; a concrete
negative-identity cross map witnesses that they need not be channels. -/
theorem equivalent_instrument
    {E : Type*} [Fintype E] [DecidableEq E] (e : E)
    (U0 : Matrix.unitaryGroup (Bool × E) ℂ) (V : Matrix.unitaryGroup E ℂ)
    (rho : QOp) (hrho : IsDensityMatrix rho) :
    let U := (U0 : Matrix (Bool × E) (Bool × E) ℂ)
    let U1 := Matrix.kronecker (1 : QOp) (V : Matrix E E ℂ) * U
    let D := cross U U e rho
    let C01 := cross U U1 e rho
    let C10 := cross U1 U e rho
    (∀ X : QOp, cross U1 U1 e X = cross U U e X) ∧
    (∀ X Y : QOp, cross U U1 e (X + Y) = cross U U1 e X + cross U U1 e Y) ∧
    (∀ (c : ℂ) (X : QOp), cross U U1 e (c • X) = c • cross U U1 e X) ∧
    (∀ X Y : QOp, cross U1 U e (X + Y) = cross U1 U e X + cross U1 U e Y) ∧
    (∀ (c : ℂ) (X : QOp), cross U1 U e (c • X) = c • cross U1 U e X) ∧
    jointCS (hadamardProjector false) U U1 e rho = controlBlocks D D C01 C10 ∧
    (∀ minus : Bool,
      selectControl (jointCS (hadamardProjector false) U U1 e rho) minus =
        branch U U1 e minus rho ∧
      branch U U1 e minus rho = (1 / 2 : ℂ) • D +
        ((outcomeSign minus / 4 : ℝ) : ℂ) • (C01 + C10) ∧
      IsCP (branch U U1 e minus) ∧
      0 ≤ (branch U U1 e minus rho).trace.re ∧
      (branch U U1 e minus rho).trace.re ≤ 1 ∧
      (0 < (branch U U1 e minus rho).trace.re →
        IsDensityMatrix (normalize (branch U U1 e minus rho)))) ∧
    (branch U U1 e false rho).trace.re + (branch U U1 e true rho).trace.re = 1 ∧
    (¬ IsChannel (cross (1 : QQOp) (-1 : QQOp) false)) := by sorry

end

end QAlgorithms.Papers.Independent.Information100.P48
