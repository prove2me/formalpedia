-- Prove2me | Theorems.Thm_UnivESD_Universality_lemma_1_7
-- name    : UnivESD.Universality.lemma_1_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T02:18:22.663329+00:00
-- url     : https://prove2.me/theorems/70223dbd-6164-45f1-9b54-6aff376ba3c0
-- title:
--   Lemma 1.7 (tightness of ESDs): $\frac1{n^2}\|A_n\|_2^2$ and $\int|z|^2\,d\mu_{A_n/\sqrt n}$ are almost surely bounded
-- statement:
--   Let $x$ be a complex random variable with zero mean and unit variance, let $X_n=(x_{ij})_{1\le i,j\le n}$ have i.i.d. entries distributed as $x$, let $M_n$ be deterministic $n\times n$ matrices satisfying (1.3), $\sup_n n^{-2}\|M_n\|_2^2<\infty$, and set $A_n=M_n+X_n$. Then the quantities
--   $$\frac1{n^2}\|A_n\|_2^2\qquad\text{and}\qquad\int_{\mathbb C}|z|^2\,d\mu_{\frac1{\sqrt n}A_n}(z)$$
--   are almost surely bounded (and hence also bounded in probability).
--
--   Tightness is what allows the passage between vague convergence of the ESDs and convergence of their characteristic functions or log-potentials; it is hypothesis (i) of the replacement principle.
--
--   **Formalization Note.** The $X_n$ are the corners of one infinite i.i.d. array (the paper's proof applies the strong law of large numbers to $\frac1{n^2}\|X_n\|_2^2$). "Almost surely bounded" means: with probability one there is $C$ with the quantity at most $C$ for all large $n$. The parenthetical "hence bounded in probability" is a consequence and is not stated separately.
-- source:
--   Tao, Vu, Random matrices: Universality of ESDs and the circular law, Ann. Probab. 38 (2010), no. 5, p. 2027 (PDF 5), Lemma 1.7

import Mathlib
import Definitions.Def_UnivESD_Universality_Basic
import Definitions.Def_UnivESD_Universality_Model

open MeasureTheory Filter Topology

namespace UnivESD.Universality

/-- Lemma 1.7 (tightness of ESDs), p. 2027. -/
theorem lemma_1_7 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (xs : ℕ → ℕ → Ω → ℂ) (hx : IsIIDArray P xs)
    (M : (n : ℕ) → Matrix (Fin n) (Fin n) ℂ) (hM : ShiftBound M) :
    ASBounded P (fun n ω => (1 / (n : ℝ) ^ 2) * hsNormSq (M n + cornerMatrix xs n ω)) ∧
      ASBounded P (fun n ω => ∫ z, ‖z‖ ^ 2 ∂esd (invSqrt n • (M n + cornerMatrix xs n ω))) := by sorry

end UnivESD.Universality
