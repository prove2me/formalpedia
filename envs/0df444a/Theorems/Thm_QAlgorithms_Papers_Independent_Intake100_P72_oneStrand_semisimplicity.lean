-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P72_oneStrand_semisimplicity
-- name    : QAlgorithms.Papers.Independent.Intake100.P72.oneStrand_semisimplicity
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T14:48:30.433778+00:00
-- url     : https://prove2.me/theorems/8f00a1da-79d6-45b9-849f-565c478c56e3
-- title:
--   One-strand semisimplicity criterion
-- statement:
--   Let $F$ be a field over which $X^m-1$ splits, let $m>1$ be an integer, and let $\delta:\mathbb Z/m\mathbb Z\to F$ be the periodic family of loop parameters. Write $B_{m,1}(\delta)$ for the cyclotomic Brauer algebra defined by the presentation on page 3. Then
--
--   $$
--   B_{m,1}(\delta)\text{ is semisimple}
--   \quad\Longleftrightarrow\quad
--   (m:F)\ne0
--   \quad\Longleftrightarrow\quad
--   B_{m,1}(\delta)\text{ is split semisimple}.
--   $$
--
--   Split semisimplicity means that the algebra admits an $F$-algebra isomorphism to a finite product of full matrix algebras over $F$, with positive block sizes. The middle condition holds in characteristic zero, and in positive characteristic $p$ means $p\nmid m$. This isolates the one-strand case, whose presentation has only the generator $t_1$ and relation $t_1^m=1$.
-- source:
--   On the semisimplicity of cyclotomic Baruer algebras, II, arXiv:math/0702633v1, PDF p. 2, Theorem A c

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P72

noncomputable section

namespace QAlgorithms.Papers.Independent.Intake100.P72

universe u v

open QAlgorithms.Papers.Independent.Renew46.P16 (BMWLetter freeS freeE freeX)

/-- Theorem A(c), arXiv:math/0702633v1, PDF p.2; proof attribution on p.15.
Each of ordinary and split semisimplicity is equivalent to e not dividing m.
The field only has to split X^m-1; no primitive root is required in bad
characteristic. The cast condition also covers characteristic zero. -/
theorem oneStrand_semisimplicity
    (F : Type u) [Field F] (m : ℕ) (delta : ZMod m → F) (hm : 1 < m)
    (hsplit : (Polynomial.X ^ m - 1 : Polynomial F).Splits) :
    (IsSemisimpleRing (CyclotomicBrauer F m 1 delta) ↔ (m : F) ≠ 0) ∧
      (HasSplitWedderburn F (CyclotomicBrauer F m 1 delta) ↔ (m : F) ≠ 0) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P72

end
