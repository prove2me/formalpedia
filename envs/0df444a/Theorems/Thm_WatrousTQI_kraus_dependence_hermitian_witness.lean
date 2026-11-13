-- Prove2me | Theorems.Thm_WatrousTQI_kraus_dependence_hermitian_witness
-- name    : WatrousTQI.kraus_dependence_hermitian_witness
-- status  : Open
-- author  : @Mrnaiq
-- created : 2026-11-12T22:35:36.132946+00:00
-- url     : https://prove2.me/theorems/cae8d23e-e767-41a8-9f09-145c51fff77c
-- title:
--   Theorem 2.31 proof — Hermitian witness for Kraus-product dependence
-- statement:
--   For positive input and output dimensions and a nonempty finite family $A_0,\ldots,A_{m-1}$ of rectangular complex matrices, complex linear dependence of the indexed family $(A_b^\dagger A_a)_{a,b}$ yields a nonzero Hermitian coefficient matrix: $$\exists H=H^\dagger\ne0:\quad\sum_{a,b}H_{ab}A_b^\dagger A_a=0.$$ This algebraic step does not require channel normalization or independence of the original Kraus operators. It is extracted from equations (2.184)–(2.187), whose argument uses neither condition.
-- source:
--   John Watrous, The Theory of Quantum Information, Cambridge University Press, 2018, Section 2.2.4, printed pp.96–99. https://cs.uwaterloo.ca/~watrous/TQI/TQI.pdf; Proof of Theorem 2.31, equations (2.184)–(2.187), printed p.98.

import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Matrix ComplexConjugate ComplexOrder BigOperators

namespace WatrousTQI
theorem kraus_dependence_hermitian_witness {dx dy m : ℕ}
    (hdx : 0 < dx) (hdy : 0 < dy) (hm : 0 < m)
    (A : Fin m → Matrix (Fin dy) (Fin dx) ℂ)
    (hdep : ¬ LinearIndependent ℂ (fun ab : Fin m × Fin m => (A ab.2)ᴴ * A ab.1)) :
    ∃ H : Matrix (Fin m) (Fin m) ℂ,
      H.IsHermitian ∧ H ≠ 0 ∧ ∑ a, ∑ b, H a b • ((A b)ᴴ * A a) = 0 := by sorry
end WatrousTQI
