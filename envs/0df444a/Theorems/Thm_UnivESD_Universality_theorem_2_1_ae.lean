-- Prove2me | Theorems.Thm_UnivESD_Universality_theorem_2_1_ae
-- name    : UnivESD.Universality.theorem_2_1_ae
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T02:18:56.387886+00:00
-- url     : https://prove2.me/theorems/ee005ec7-0b60-45a7-b00c-151e0f16c1f6
-- title:
--   Theorem 2.1 (replacement principle, almost sure version)
-- statement:
--   Suppose, for each $n$, that $A_n,B_n\in M_n(\mathbb C)$ are random matrices on a common probability space. Assume:
--
--   1. the expression $\frac1{n^2}\|A_n\|_2^2+\frac1{n^2}\|B_n\|_2^2$ is almost surely bounded;
--   2. for almost all complex numbers $z$,
--   $$\frac1n\log\Bigl|\det\Bigl(\frac1{\sqrt n}A_n-zI\Bigr)\Bigr|-\frac1n\log\Bigl|\det\Bigl(\frac1{\sqrt n}B_n-zI\Bigr)\Bigr|$$
--   converges almost surely to zero and, in particular, these determinants are almost surely nonzero for all but finitely many $n$.
--
--   Then $\mu_{\frac1{\sqrt n}A_n}-\mu_{\frac1{\sqrt n}B_n}$ converges almost surely to zero: with probability one, $\int f\,d\mu_{\frac1{\sqrt n}A_n}-\int f\,d\mu_{\frac1{\sqrt n}B_n}\to0$ for every continuous compactly supported $f:\mathbb C\to\mathbb R$.
--
--   This is the "resp." half of Theorem 2.1, used for the almost-sure universality statement.
--
--   **Formalization Note.** Because $\log 0=0$ in Lean, the nonvanishing clause is stated explicitly for almost every $z$: almost surely both determinants are nonzero for all large $n$. The entries of $A_n,B_n$ are assumed measurable.
-- source:
--   Tao, Vu, Random matrices: Universality of ESDs and the circular law, Ann. Probab. 38 (2010), no. 5, p. 2034 (PDF 12), Theorem 2.1 (almost sure version)

import Mathlib
import Definitions.Def_UnivESD_Universality_Basic
import Definitions.Def_UnivESD_Universality_Model

open MeasureTheory Filter Topology

namespace UnivESD.Universality

/-- Theorem 2.1 (replacement principle), almost sure convergence, p. 2034. -/
theorem theorem_2_1_ae {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (A B : (n : ℕ) → Ω → Matrix (Fin n) (Fin n) ℂ)
    (hA : ∀ n (i j : Fin n), Measurable fun ω => A n ω i j)
    (hB : ∀ n (i j : Fin n), Measurable fun ω => B n ω i j)
    (h1 : ASBounded P fun n ω =>
      (1 / (n : ℝ) ^ 2) * hsNormSq (A n ω) + (1 / (n : ℝ) ^ 2) * hsNormSq (B n ω))
    (h2 : ∀ᵐ z ∂(volume : Measure ℂ),
      (∀ᵐ ω ∂P, Tendsto (fun n => normLogDet (A n ω) z - normLogDet (B n ω) z) atTop (𝓝 0)) ∧
        ∀ᵐ ω ∂P, ∀ᶠ n : ℕ in atTop,
          (invSqrt n • A n ω - z • (1 : Matrix (Fin n) (Fin n) ℂ)).det ≠ 0 ∧
            (invSqrt n • B n ω - z • (1 : Matrix (Fin n) (Fin n) ℂ)).det ≠ 0) :
    ESDDiffTendstoAS P A B := by sorry

end UnivESD.Universality
