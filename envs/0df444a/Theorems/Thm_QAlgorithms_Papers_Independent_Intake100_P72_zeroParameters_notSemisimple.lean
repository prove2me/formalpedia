-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P72_zeroParameters_notSemisimple
-- name    : QAlgorithms.Papers.Independent.Intake100.P72.zeroParameters_notSemisimple
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T14:49:34.756379+00:00
-- url     : https://prove2.me/theorems/5cad32c4-bef1-4405-9ac3-a73839d4b06e
-- title:
--   Zero-parameter algebras are not semisimple
-- statement:
--   Let $F$ be a field over which $X^m-1$ splits. Let $m>1$ and $n\ge2$ be integers, and set every periodic loop parameter equal to zero. Then
--
--   $$
--   B_{m,n}(0)\text{ is not semisimple and is not split semisimple}.
--   $$
--
--   Here split semisimplicity means the existence of an $F$-algebra isomorphism to a finite product of full matrix algebras over $F$, with positive block sizes. The conclusion applies in every characteristic, including characteristics dividing $m\,n!$. This is the zero-parameter clause of the main theorem, retained under its numbered statement.
-- source:
--   On the semisimplicity of cyclotomic Baruer algebras, II, arXiv:math/0702633v1, PDF p. 14, Theorem 4.8

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P72

noncomputable section

namespace QAlgorithms.Papers.Independent.Intake100.P72

universe u v

open QAlgorithms.Papers.Independent.Renew46.P16 (BMWLetter freeS freeE freeX)

/-- Theorem 4.8, arXiv:math/0702633v1, PDF p.14 (Theorem A(b) on p.2).
Every zero-parameter algebra with m>1 and n≥2 over a splitting field fails
both ordinary and split semisimplicity, including in bad characteristic. -/
theorem zeroParameters_notSemisimple
    (F : Type u) [Field F] (m n : ℕ) (hm : 1 < m) (hn : 2 ≤ n)
    (hsplit : (Polynomial.X ^ m - 1 : Polynomial F).Splits) :
    ¬ IsSemisimpleRing (CyclotomicBrauer F m n (fun _ => 0)) ∧
      ¬ HasSplitWedderburn F (CyclotomicBrauer F m n (fun _ => 0)) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P72

end
