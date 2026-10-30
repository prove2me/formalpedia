-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P43_output_program_independence
-- name    : QAlgorithms.Papers.Independent.Extend50.P43.output_program_independence
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T20:59:01.803439+00:00
-- url     : https://prove2.me/theorems/d7626899-336a-4e8c-89a9-eaf8b9e911e5
-- title:
--   The residual program is independent of the data
-- statement:
--   Let $G$ be a fixed unitary on $m$ data qubits and $n$ program qubits, let $U$ be a unitary on the data register, and let $P$ be a normalized program. Assume that for every normalized data vector $d$ there exists a normalized residual program $q_d$ satisfying $G(d\otimes P)=Ud\otimes q_d$. Then there is one normalized residual program $q$ such that
--
--   $$
--   G(d\otimes P)=Ud\otimes q\qquad\text{for every normalized }d.
--   $$
--
--   This justifies using one residual program for a selected operation. In particular, the hypothesis allows the residual witness to depend on the input, while the conclusion removes that dependence.
-- source:
--   Programmable quantum gate arrays, arXiv:quant-ph/9703032v1, PDF p. 1, Unnumbered supporting result after Eqs.(3)-(5): residual program is independent of data

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P43

namespace QAlgorithms.Papers.Independent.Extend50.P43

open scoped ComplexConjugate

noncomputable section

/-- PDF p.1, paragraph after Eqs.(3)–(5): the output program is independent
of the data. The source's inner-product cancellation omits orthogonal inputs;
linearity and a superposition connect those inputs without a new hypothesis. -/
theorem output_program_independence (m n : ℕ)
    (G : Matrix (Qubits m × Qubits n) (Qubits m × Qubits n) ℂ)
    (hG : G ∈ Matrix.unitaryGroup (Qubits m × Qubits n) ℂ)
    (U : Matrix (Qubits m) (Qubits m) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Qubits m) ℂ)
    (P : EuclideanSpace ℂ (Qubits n)) (hImplements : ImplementsProgramUnitary G U P) :
    ∃ q : EuclideanSpace ℂ (Qubits n), IsState q ∧
      ∀ d : EuclideanSpace ℂ (Qubits m), IsState d →
        act G (tensorVec d P) = tensorVec (act U d) q := by sorry

end

end QAlgorithms.Papers.Independent.Extend50.P43
