-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P67_relational_coordinates
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P67.relational_coordinates
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T08:57:06.630203+00:00
-- url     : https://prove2.me/theorems/a42594ea-136f-4c7f-a257-764fc651fa0e
-- title:
--   §III E–F, Eqs.(34)–(35): coherent relational-coordinate expansion
-- statement:
--   Fix normalized sample vectors, an anchor $\phi_a$, a unit input $\psi$, and a finite history $k_1,\ldots,k_T$. Set $\psi_0=\psi$ and $\psi_{t+1}=R(k_{t+1})(I-|\phi_a\rangle\langle\phi_a|)\psi_t$. With unary address $|t\rangle=|1\rangle^{\otimes t}|0\rangle^{\otimes(T-t)}$, the actual ordered erasure unitary satisfies
--
--   $$W_T\cdots W_1(|\psi\rangle|-\rangle^{\otimes T})=|\phi_a\rangle\otimes\sum_{t=0}^{T-1}\langle\phi_a|\psi_t\rangle|t\rangle+|\psi_T\rangle\otimes|T\rangle.$$
--
--   Every coefficient is unchanged when the same unitary transforms the input, all samples and the anchor. The residual is retained at finite $T$; neither algebra generation nor a successful erasure assumption is needed for this exact expansion.
-- source:
--   Universal Quantum Emulator, arXiv:1606.02734v2, PDF p. 8, §III E–F, Eqs.(34)–(35): coherent relational-coordinate expansion

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P67

noncomputable section

open scoped ComplexConjugate Matrix Matrix.Norms.L2Operator

attribute [local instance] Classical.propDecidable

open MeasureTheory Filter

namespace QAlgorithms.Papers.Independent.Intakethird100.P67

variable {I J K L A : Type*} [Fintype I] [DecidableEq I]
  [Fintype J] [DecidableEq J] [Fintype K] [DecidableEq K]
  [Fintype L] [DecidableEq L] [Fintype A] [DecidableEq A]

/-- PDF pp.8–9, Eqs.(34)–(35): complete coherent expansion and simultaneous-unitary
invariance of its coordinates, including transformation of the anchor. -/
theorem relational_coordinates (phi : K → EuclideanSpace ℂ I) (a : K)
    (hphi : ∀ k, IsState (phi k)) (T : ℕ) (h : Fin T → K)
    (psi : EuclideanSpace ℂ I) (hpsi : IsState psi) :
    act (historyUnitary (erasureGate phi a) h) (tensorVec psi (minusRegister T)) =
      coordinateExpansion phi a h psi ∧
    (∀ (U : Matrix.unitaryGroup I ℂ) (t : ℕ),
      inner ℂ (act (U : Matrix I I ℂ) (phi a))
        (residual (fun k => act (U : Matrix I I ℂ) (phi k)) a (act (U : Matrix I I ℂ) psi)
          ((List.ofFn h).take t)) =
      inner ℂ (phi a) (residual phi a psi ((List.ofFn h).take t))) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P67

end
