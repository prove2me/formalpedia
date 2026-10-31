-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P12_finite_basis_reduction
-- name    : QAlgorithms.Papers.Independent.Intake100.P12.finite_basis_reduction
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T13:00:54.243951+00:00
-- url     : https://prove2.me/theorems/302f8825-7c65-4500-9458-640fe4a6a66b
-- title:
--   Finite exact tests from actual unitary inputs
-- statement:
--   For integers $d,k\ge1$, there is a finite family $U_1,\ldots,U_n\in U(d)$ whose repeated-channel Choi matrices are linearly independent and span $V_{d,k}:=\operatorname{span}_{\mathbb C}\{C(U^{\otimes k}):U\in U(d)\}$. For every linear unitary-channel target $f$, process matrix $S$, and real coefficient $p$,
--
--   $$[\forall i,\ \mathcal L_S(C(U_i^{\otimes k}))=p f(C(U_i))]\ \Longleftrightarrow\ [\forall U\in U(d),\ \mathcal L_S(C(U^{\otimes k}))=p f(C(U))].$$
--
--   Here Choi matrices and the contraction use the fixed source bases and unnormalized convention. This converts exact universal testing into exact finite testing; no arbitrary ambient matrix basis or nonlinear target is substituted.
-- source:
--   Probabilistic exact universal quantum circuits for transforming unitary operations, arXiv:1909.01366v2, PDF p. 7, III, Eqs. (17)–(19)

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P12

noncomputable section

open QAlgorithms

open scoped Matrix ComplexConjugate ComplexOrder Kronecker

namespace QAlgorithms.Papers.Independent.Intake100.P12

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

open QAlgorithms.Papers.Independent.Dependency50.P26 (ChannelChoi)

/-- PDF p.7, Eqs. (17)–(19): finitely many actual unitary inputs suffice;
linearity of the single-channel target is essential, and k=0 is excluded. -/
theorem finite_basis_reduction {d k : ℕ} (hd : 0 < d) (hk : 0 < k) :
    ∃ n : ℕ, ∃ B : Fin n → Matrix.unitaryGroup (Fin d) ℂ,
      IsUnitaryBasis d k n B ∧
      ∀ (f : Op (Fin d × Fin d) →ₗ[ℂ] Op (Fin d × Fin d)),
        UnitaryLinearTarget f → ∀ (S : Op (ProcessBasis (uniformWires d k))) (p : ℝ),
        (∀ i, evaluateOracleSlots S (repeatedChoi k (B i)) = (p : ℂ) • f (gateChoi (B i : Op (Fin d)))) ↔
          ExactUnitarySuccess S (fun U => f (gateChoi (U : Op (Fin d)))) p := by sorry

end QAlgorithms.Papers.Independent.Intake100.P12

end
