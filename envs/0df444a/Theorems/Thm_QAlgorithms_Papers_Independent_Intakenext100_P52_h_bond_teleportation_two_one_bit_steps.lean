-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P52_h_bond_teleportation_two_one_bit_steps
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P52.h_bond_teleportation_two_one_bit_steps
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T23:46:01.324666+00:00
-- url     : https://prove2.me/theorems/6a7434a5-4026-4ae4-b79a-0323c064416e
-- title:
--   §7: uniform CZ one-bit decomposition of teleportation
-- statement:
--   Let $|H\rangle=CZ|++\rangle$ and $|h_{cd}\rangle=(X^dZ^c\otimes I)|H\rangle$. These four kets are orthonormal, and $CZ|h_{cd}\rangle$ has the same density as $|x_c\rangle|x_d\rangle$, where $|x_s\rangle=(|0\rangle+(-1)^s|1\rangle)/\sqrt2$. For every normalized input, teleportation using resource $|H\rangle$ and measurement ket $|h_{cd}\rangle$ has the same surviving branch density as two successive $CZ$-plus-$X$ one-bit steps:
--
--   $$ |b_{cd}\rangle\langle b_{cd}|=\tfrac14 X^dZ^c|\psi\rangle\langle\psi|Z^cX^d,\qquad\Pr(c,d)=\tfrac14. $$
--
--   **Source correction:** in the ordered $I,X,Z,XZ$ list, the local $X$-basis rays are $++,+-,-+,--$. The printed list swaps the last two labels; branch phases are absorbed by densities.
-- source:
--   An introduction to measurement based quantum computation, arXiv:quant-ph/0508124v2, PDF p. 16, §7: uniform CZ one-bit decomposition of teleportation

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P52

noncomputable section

open scoped Matrix ComplexConjugate

namespace QAlgorithms.Papers.Independent.Intakenext100.P52

open QAlgorithms.Papers.Independent.Information100.P21 (Vec)

open QAlgorithms.Papers.Independent.Gap20.P01 (applyRect)

/-- Common one-bit primitive, PDF p.16. Printed CZ basis list swaps its last
two ray labels: corrected I,X,Z,XZ labels are ++,+-,-+,--, up to phase.
The H-bond teleportation instrument equals the two sequential CZ/X steps. -/
theorem h_bond_teleportation_two_one_bit_steps :
    Orthonormal ℂ (fun p : QubitPair => hBell p.1 p.2) ∧
    (∀ c d : Bool, pureDensity (act (controlled pauliZ) (hBell c d)) =
      pureDensity (tensorVec (equatorial 0 c) (equatorial 0 d))) ∧
    (∀ (psi : Vec Bool), IsState psi → ∀ c d : Bool,
      let v := teleportContraction psi hBond (hBell c d)
      pureDensity v = pureDensity (lineBranch 2 (fun _ => 0) ![c,d] psi) ∧
      pureDensity v = (1 / 4 : ℝ) • pureDensity (act (pauliByproduct d c) psi) ∧
      ‖v‖ ^ 2 = (1 / 4 : ℝ)) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P52

end
