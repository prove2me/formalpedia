-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P52_one_bit_teleportation
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P52.one_bit_teleportation
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T23:40:41.097857+00:00
-- url     : https://prove2.me/theorems/9baa4683-68a6-46d9-915a-08d33dc05d06
-- title:
--   §5 Figures 6–7: elementary one-bit teleportation
-- statement:
--   Let $|\psi\rangle$ be a normalized input, adjoin $|+\rangle$, apply $CZ$, and destructively measure the first site in the ordered basis $M(\theta)=\{(|0\rangle+(-1)^s e^{i\theta}|1\rangle)/\sqrt2:s=0,1\}$. With $W(\theta)=H\operatorname{diag}(1,e^{i\theta})$, the surviving branch is
--
--   $$ |b_s\rangle=\frac1{\sqrt2}X^sW(-\theta)|\psi\rangle,\qquad\Pr(s)=\frac12. $$
--
--   For $\theta=0$ this is $X^sH|\psi\rangle/\sqrt2$. A three-site line with two $X$ measurements has branch $X^{s_2}Z^{s_1}|\psi\rangle/2$. These are the elementary normalized-resource primitives for the cluster constructions.
-- source:
--   An introduction to measurement based quantum computation, arXiv:quant-ph/0508124v2, PDF p. 9, §5 Figures 6–7: elementary one-bit teleportation

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P52

noncomputable section

open scoped Matrix ComplexConjugate

namespace QAlgorithms.Papers.Independent.Intakenext100.P52

open QAlgorithms.Papers.Independent.Information100.P21 (Vec)

open QAlgorithms.Papers.Independent.Gap20.P01 (applyRect)

/-- Figures 6–7, PDF pp.9–10: negative angle and branch normalization retained.
The two X-measurement chain is included in source Pauli order X^(s2) Z^(s1). -/
theorem one_bit_teleportation (psi : Vec Bool) (hpsi : IsState psi) :
    (∀ theta : ℝ, ∀ s : Bool,
      let b := lineBranch 1 (fun _ => theta) (fun _ => s) psi
      b = ((Real.sqrt 2)⁻¹ : ℂ) • act (pauliX ^ s.toNat * wGate (-theta)) psi ∧
      ‖b‖ ^ 2 = (1 / 2 : ℝ)) ∧
    (∀ s : Bool, lineBranch 1 (fun _ => 0) (fun _ => s) psi =
      ((Real.sqrt 2)⁻¹ : ℂ) • act (pauliX ^ s.toNat * hadamard) psi) ∧
    (∀ s : Fin 2 → Bool, lineBranch 2 (fun _ => 0) s psi =
      (1 / 2 : ℂ) • act (pauliByproduct (s 1) (s 0)) psi) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P52

end
