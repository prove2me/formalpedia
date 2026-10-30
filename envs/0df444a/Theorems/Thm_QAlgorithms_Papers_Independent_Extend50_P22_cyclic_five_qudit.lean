-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P22_cyclic_five_qudit
-- name    : QAlgorithms.Papers.Independent.Extend50.P22.cyclic_five_qudit
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T17:29:16.537897+00:00
-- url     : https://prove2.me/theorems/785abfe3-04e2-42c5-8e30-3f2eef931dc6
-- title:
--   Unnumbered cyclic five-qudit perfect-tensor construction, Eqs.(42)–(43)
-- statement:
--   Let $D\ge2$ and let $\omega$ be a primitive $D$th root of unity. With all labels in $\mathbb Z_D$, define the normalized five-site encoding by $$V|x\rangle=D^{-2}\sum_{j+k+l+m+n=x}\omega^{jk+kl+lm+mn+nj}|j,k,l,m,n\rangle.$$ It is an isometry, corrects erasure of any two sites by a CPTP recovery chosen before the input, and satisfies $Z^{\otimes5}V=VZ$, where $Z|k\rangle=\omega^k|k\rangle$. It fails covariance for the natural continuous integer-lift charge action. Finite cyclic covariance is not promoted to a continuous symmetry.
-- source:
--   Continuous symmetries and approximate quantum error correction, arXiv:1902.07714v1, PDF p. 12, Unnumbered cyclic five-qudit perfect-tensor construction, Eqs.(42)–(43)

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P22

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

namespace QAlgorithms.Papers.Independent.Extend50.P22

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P22 (bell)

open QAlgorithms.Papers.Independent.Support21.P09 (Irreducible)

open QAlgorithms.Papers.Independent.Renew46.P45 (symmetricWeight)

/-- PDF pp.12–13, (42),(43): exact two-erasure correction, cyclic Z_D covariance,
and failure of the natural continuous U(1) covariance. The last clause concerns the
natural integer lifts of the charges, not every possible group action. -/
theorem cyclic_five_qudit (D : ℕ) [NeZero D] (hD : 2 ≤ D) (omega : ℂ)
    (homega : IsPrimitiveRoot omega D) :
    let V := fiveQuditEncoding D omega
    Vᴴ * V = 1 ∧
    (∀ S : Finset (Fin 5), S.card ≤ 2 → CorrectsUniformErasure V (fun _ => 0) S) ∧
    (Matrix.diagonal (fun y : Fin 5 → ZMod D => ∏ i, omega ^ (y i).val)) * V =
      V * Matrix.diagonal (fun x : ZMod D => omega ^ x.val) ∧
    ¬ (∀ theta : ℝ, ∀ X : Matrix (ZMod D) (ZMod D) ℂ,
      conjSuperop V (conjSuperop (chargeEvolution (quditCharge D) theta) X) =
        conjSuperop (chargeEvolution
          (Matrix.diagonal (fun y : Fin 5 → ZMod D => ∑ i, ((y i).val : ℂ))) theta)
          (conjSuperop V X)) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P22

end
