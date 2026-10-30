-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P43_no_deterministic_universal_array
-- name    : QAlgorithms.Papers.Independent.Extend50.P43.no_deterministic_universal_array
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T20:59:40.990997+00:00
-- url     : https://prove2.me/theorems/dac15e1f-17b8-4370-a4b1-5f16907773e3
-- title:
--   No finite deterministic exact universal array
-- statement:
--   Let $m\geq1$ and $n\geq0$ be integers, and let $G$ be any fixed unitary on an $m$-qubit data register and an $n$-qubit program register. It is impossible for every data-register unitary to admit a normalized program implementing it exactly on all normalized data inputs:
--
--   $$
--   \neg\Bigl[\forall U\text{ unitary},\ \exists P\text{ normalized},\ \forall d\text{ normalized},\ \exists q_d\text{ normalized}:\ G(d\otimes P)=Ud\otimes q_d\Bigr].
--   $$
--
--   The impossibility concerns a finite deterministic exact processor. The requirement $m\geq1$ makes explicit the source's implicit nontrivial data register.
-- source:
--   Programmable quantum gate arrays, arXiv:quant-ph/9703032v1, PDF p. 1, Unnumbered corollary: no finite deterministic universal quantum array

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P43

namespace QAlgorithms.Papers.Independent.Extend50.P43

open scoped ComplexConjugate

noncomputable section

/-- PDF pp.1–2, repeated on p.3: no finite deterministic exact universal
array exists for a nontrivial data register. At m=0 all unitaries are scalar,
so the implicit nontrivial-register assumption is made explicit. -/
theorem no_deterministic_universal_array (m n : ℕ) (hm : 1 ≤ m)
    (G : Matrix (Qubits m × Qubits n) (Qubits m × Qubits n) ℂ)
    (hG : G ∈ Matrix.unitaryGroup (Qubits m × Qubits n) ℂ) :
    ¬ (∀ U : Matrix (Qubits m) (Qubits m) ℂ,
      U ∈ Matrix.unitaryGroup (Qubits m) ℂ →
        ∃ P : EuclideanSpace ℂ (Qubits n), ImplementsProgramUnitary G U P) := by sorry

end

end QAlgorithms.Papers.Independent.Extend50.P43
