-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P12_identical_unitary_switch
-- name    : QAlgorithms.Papers.Independent.Intake100.P12.identical_unitary_switch
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T13:11:19.484293+00:00
-- url     : https://prove2.me/theorems/6681a265-e7cf-4d7d-9785-b866781d2ce7
-- title:
--   Identical slots make a controlled switch trivial
-- statement:
--   Let $d\ge1$, $k\ge0$ and $U\in U(d)$. Consider the switch that coherently controls every permutation of the $k$ slot orders, leaving the permutation label unchanged. If every slot contains $U$, its matrix is
--
--   $$W(U,\ldots,U)=I_{\rm order}\otimes U^k.$$
--
--   Consequently the system undergoes the channel of $U^k$, and arbitrary coherent order registers are preserved. This concerns the controlled-permutation switch; it does not identify all general processes with switches.
-- source:
--   Probabilistic exact universal quantum circuits for transforming unitary operations, arXiv:1909.01366v2, PDF p. 17, VI F

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P12

noncomputable section

open QAlgorithms

open scoped Matrix ComplexConjugate ComplexOrder Kronecker

namespace QAlgorithms.Papers.Independent.Intake100.P12

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

open QAlgorithms.Papers.Independent.Dependency50.P26 (ChannelChoi)

/-- PDF p.17, VI F: identical slots collapse every coherently controlled
permutation to identity on the order register tensored with U^k. -/
theorem identical_unitary_switch {d k : ℕ} (hd : 0 < d)
    (U : Matrix.unitaryGroup (Fin d) ℂ) :
    switchMatrix (k := k) (fun _ => (U : Op (Fin d))) =
      (1 : Op (Equiv.Perm (Fin k))) ⊗ₖ ((U : Op (Fin d))^k) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P12

end
