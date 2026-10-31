-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P22_covariance_and_trace
-- name    : QAlgorithms.Papers.Independent.Intake100.P22.covariance_and_trace
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T16:44:49.386168+00:00
-- url     : https://prove2.me/theorems/d396c65e-f2b6-4e2a-8e4e-b19766aef377
-- title:
--   Regular covariance update and complex signed trace identities
-- statement:
--   Fix a finite number $n\ge0$ of fermionic modes. Let $\mathcal C_{2n}=\operatorname{End}(\mathbb C^{2^n})$ have Hermitian Majorana generators $c_a$ satisfying $c_ac_b+c_bc_a=2\delta_{ab}I$. The symbol map $\omega$ sends each ordered Majorana monomial linearly to the corresponding ordered Grassmann monomial; it is not multiplicative. Gaussian states, operators, and maps have the meanings of Definitions 1–3 of the paper. All maps act on the full complex operator algebra, including its odd sector.
--
--   Let $E$ have kernel parameters $(A,B,D,C)$ and let $X$ be a regular Gaussian operator with complex skew covariance $M$ and $\operatorname{Tr}X\ne0$. Then, without any inverse assumption,
--   $$
--   \operatorname{Tr}(E(X))^2=C^2\det(I+MD)\operatorname{Tr}(X)^2.
--   $$
--   If $\det M\ne0$, the signed trace is
--   $$
--   \operatorname{Tr}(E(X))=C(-1)^n\operatorname{Pf}(M)\operatorname{Pf}(M^{-1}+D)\operatorname{Tr}(X).
--   $$
--   Independently of whether $M$ is invertible, if $\det(I+MD)\ne0$ and $C\ne0$, the output is regular with covariance
--   $$
--   M'=B(I+MD)^{-1}MB^T+A.
--   $$
--   On the further domain $\det M\ne0$, this also equals $B(M^{-1}+D)^{-1}B^T+A$. Covariance of a regular $Y$ means $i\operatorname{Tr}(Y[c_a,c_b])/(2\operatorname{Tr}Y)$. All traces and squares here are complex algebraic quantities. These identities keep both output shape and its signed normalization.
-- source:
--   Lagrangian representation for fermionic linear optics, arXiv:quant-ph/0404180v2, PDF p. 9, §VI, Eqs.(45)–(47): covariance update and signed normalization

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P22

noncomputable section

open scoped BigOperators Matrix ComplexConjugate ComplexOrder

namespace QAlgorithms.Papers.Independent.Intake100.P22

open QAlgorithms.Papers.Independent.Advance50.P19
  (CARSystem Major monomial wick totalFermionParity)

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF p.9, Eqs.(45)-(47): complex algebraic trace square, signed trace, and
regular covariance update. The two inverse domains are guarded separately.
C=0 is allowed in both trace identities but excluded for a regular output. -/
theorem covariance_and_trace {n : ℕ} (s : CARSystem n)
    (E : Superop (Qubits n) (Qubits n)) (K : GrassmannKernel n) (hE : HasGrassmannKernel s E K)
    (X : Op (Qubits n)) (M : Matrix (Major n) (Major n) ℂ) (hX : RegularWith s X M) :
    (E X).trace ^ 2 = K.C ^ 2 * (1 + M * K.D).det * X.trace ^ 2 ∧
    (M.det ≠ 0 → (E X).trace =
      K.C * (-1 : ℂ) ^ n * pfaffian M * pfaffian (M⁻¹ + K.D) * X.trace) ∧
    ((1 + M * K.D).det ≠ 0 → K.C ≠ 0 →
      RegularWith s (E X) (K.B * (1 + M * K.D)⁻¹ * M * K.B.transpose + K.A) ∧
      regularCorrelation s (E X) = K.B * (1 + M * K.D)⁻¹ * M * K.B.transpose + K.A ∧
      (M.det ≠ 0 →
        K.B * (M⁻¹ + K.D)⁻¹ * K.B.transpose + K.A =
          K.B * (1 + M * K.D)⁻¹ * M * K.B.transpose + K.A)) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P22

end
