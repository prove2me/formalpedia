-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P38_qubit_asymptotics
-- name    : QAlgorithms.Papers.Independent.Extend50.P38.qubit_asymptotics
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T14:52:38.470109+00:00
-- url     : https://prove2.me/theorems/94424eed-b899-4fe3-9d6b-431eb8bbab14
-- title:
--   Qubit classical threshold and first-order asymptotic error
-- statement:
--   Let $f_N$ be the Haar-average pure-input fidelity of teleportation with $N$ singlets and the normalized square-root measurement. Then
--
--   $$f_N>\frac23\quad(N\geq3),\qquad\lim_{N\to\infty}N(1-f_N)=\frac12.$$
--
--   The limit states the source's first-order asymptotic formula $f_N=1-1/(2N)+o(1/N)$. It retains the leading error coefficient and implies convergence to perfect average fidelity.
-- source:
--   Asymptotic teleportation scheme as a universal programmable quantum processor, arXiv:0807.4568v2, PDF p. 3, Unnumbered paragraph following exact fidelity display

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P38

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

open Filter MeasureTheory

namespace QAlgorithms.Papers.Independent.Extend50.P38

attribute [local instance] Classical.propDecidable Classical.decEq

-- Pinned accepted definitions; neither is re-declared in this module.

open QAlgorithms.Papers.Independent.Frontier18.P14 (singlet)

open QAlgorithms.Papers.Independent.Renew46.P01 (SpinPath)

/-- PDF p.3: strict classical threshold and the stated first-order asymptotic
f=1-1/(2N). The scaled error limit retains the coefficient, without inventing a remainder rate. -/
theorem qubit_asymptotics :
    (∀ N : ℕ, 3 ≤ N → 2 / 3 < qubitAverage N) ∧
    Tendsto (fun N : ℕ => (N : ℝ) * (1 - qubitAverage N)) atTop (nhds (1 / 2)) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P38

end
