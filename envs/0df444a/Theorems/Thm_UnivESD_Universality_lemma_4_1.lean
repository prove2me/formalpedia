-- Prove2me | Theorems.Thm_UnivESD_Universality_lemma_4_1
-- name    : UnivESD.Universality.lemma_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T02:19:11.294767+00:00
-- url     : https://prove2.me/theorems/a20c7131-0c6c-454b-a920-121554d95e1d
-- title:
--   Lemma 4.1 (least singular value bound): a.s. $\sigma_n(A_n),\sigma_n(B_n)\ge n^{-O(1)}$ eventually
-- statement:
--   Let $x,y$ be complex random variables with zero mean and unit variance, $X_n,Y_n$ the $n\times n$ matrices of i.i.d. copies of $x$ and $y$, $M_n$ deterministic matrices satisfying (1.3), and $A_n=M_n+X_n$, $B_n=M_n+Y_n$. Then there is a constant $C$ (depending on $x$, $y$ and the sequence $M_n$, not on $n$) such that, with probability $1$,
--   $$\sigma_n(A_n),\ \sigma_n(B_n)\ \ge\ n^{-C}$$
--   for all but finitely many $n$. In particular, with probability $1$, $A_n$ and $B_n$ are invertible for all but finitely many $n$.
--
--   The polynomial lower bound on the least singular value controls the contribution of the last rows to the log-determinant.
--
--   **Formalization Note.** $n^{-O(1)}$ is encoded as $\exists C,\ n^{-C}$ with $C$ fixed before the sample point. In §4 the lemma is applied after the shift $M_n\mapsto M_n-\sqrt n\,zI$, which preserves (1.3); the Lean statement covers every sequence satisfying (1.3). The "in particular" clause is a consequence ($n^{-C}>0$) and is not stated separately. The matrices for different $n$ come from one infinite i.i.d. array.
-- source:
--   Tao, Vu, Random matrices: Universality of ESDs and the circular law, Ann. Probab. 38 (2010), no. 5, p. 2044 (PDF 22), Lemma 4.1, (4.3)

import Mathlib
import Definitions.Def_UnivESD_Universality_Basic
import Definitions.Def_UnivESD_Universality_Model

open MeasureTheory Filter Topology

namespace UnivESD.Universality

/-- Lemma 4.1 (least singular value bound), p. 2044: almost surely
`σ_n(A_n), σ_n(B_n) ≥ n^{-O(1)}` for all but finitely many `n`. -/
theorem lemma_4_1 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (xs ys : ℕ → ℕ → Ω → ℂ) (hx : IsIIDArray P xs) (hy : IsIIDArray P ys)
    (M : (n : ℕ) → Matrix (Fin n) (Fin n) ℂ) (hM : ShiftBound M) :
    ∃ C : ℝ, ∀ᵐ ω ∂P, ∀ᶠ n : ℕ in atTop,
      (n : ℝ) ^ (-C) ≤ singVal (M n + cornerMatrix xs n ω) n ∧
        (n : ℝ) ^ (-C) ≤ singVal (M n + cornerMatrix ys n ω) n := by sorry

end UnivESD.Universality
