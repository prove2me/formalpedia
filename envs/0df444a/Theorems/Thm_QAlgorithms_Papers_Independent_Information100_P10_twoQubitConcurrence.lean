-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P10_twoQubitConcurrence
-- name    : QAlgorithms.Papers.Independent.Information100.P10.twoQubitConcurrence
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T09:39:30.126211+00:00
-- url     : https://prove2.me/theorems/8f1c4486-969e-4e5b-807c-ddb17229e7ab
-- title:
--   Two-qubit ED and concurrence, Eqs.(38)–(39)
-- statement:
--   Let $\psi=\sum_{j=0}^3w_j|j\rangle$ be a normalized pure two-qubit state, using most-significant-bit-first indices. Define its concurrence independently by the spin flip, $C(\psi)=|\langle\psi|(Y\otimes Y)\overline\psi\rangle|$. Then
--
--   $$E(\psi)=8\left[|w_0|^2|w_3|^2+|w_1|^2|w_2|^2-2\operatorname{Re}(\overline w_0\overline w_3w_1w_2)\right]=2C(\psi)^2.$$
--
--   Moreover $0\le C(\psi)\le1$, and $c\mapsto2c^2$ is strictly increasing on $[0,1]$. This exact relationship is restricted to normalized pure two-qubit states.
-- source:
--   Geometric Aspects of Entanglement, arXiv:2610.03446v1, PDF p. 5, Two-qubit ED and concurrence, Eqs.(38)–(39)

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P10

namespace QAlgorithms.Papers.Independent.Information100.P10

open scoped ComplexConjugate

/-- PDF p.5, Eqs.(38)-(39): amplitude expression and relation to spin-flip concurrence. -/
theorem twoQubitConcurrence (psi : Ket 2) (hpsi : IsState psi) :
    let w := fun j => psi (natToBits 2 j)
    entanglementDistance psi = 8 *
      (‖w 0‖ ^ 2 * ‖w 3‖ ^ 2 + ‖w 1‖ ^ 2 * ‖w 2‖ ^ 2 -
        2 * (conj (w 0) * conj (w 3) * w 1 * w 2).re) ∧
    entanglementDistance psi = 2 * concurrence psi ^ 2 ∧
    concurrence psi ∈ Set.Icc (0 : ℝ) 1 ∧
    StrictMonoOn (fun c : ℝ => 2 * c ^ 2) (Set.Icc 0 1) := by sorry

end QAlgorithms.Papers.Independent.Information100.P10
