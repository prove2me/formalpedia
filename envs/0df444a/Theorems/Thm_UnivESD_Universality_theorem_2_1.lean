-- Prove2me | Theorems.Thm_UnivESD_Universality_theorem_2_1
-- name    : UnivESD.Universality.theorem_2_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T02:18:42.289986+00:00
-- url     : https://prove2.me/theorems/00b5fba3-2db4-4d79-9493-43381f81c081
-- title:
--   Theorem 2.1 (replacement principle, in probability)
-- statement:
--   Suppose, for each $n$, that $A_n,B_n\in M_n(\mathbb C)$ are random matrices on a common probability space (no independence among their entries is required). Assume:
--
--   1. the expression $\frac1{n^2}\|A_n\|_2^2+\frac1{n^2}\|B_n\|_2^2$ is bounded in probability;
--   2. for almost all complex numbers $z$,
--   $$\frac1n\log\Bigl|\det\Bigl(\frac1{\sqrt n}A_n-zI\Bigr)\Bigr|-\frac1n\log\Bigl|\det\Bigl(\frac1{\sqrt n}B_n-zI\Bigr)\Bigr|$$
--   converges in probability to zero and, in particular, these determinants are nonzero with probability $1-o(1)$.
--
--   Then $\mu_{\frac1{\sqrt n}A_n}-\mu_{\frac1{\sqrt n}B_n}$ converges in probability to zero.
--
--   The replacement principle reduces comparison of ESDs, which are not continuous functions of the matrix in any useful sense, to comparison of normalized log-determinants.
--
--   **Formalization Note.** Lean's $\log 0=0$, so the log-determinant difference is a real number even when a determinant vanishes; the clause "the determinants are nonzero with probability $1-o(1)$" is therefore stated explicitly, inside the same almost-every-$z$ quantifier, as $\mathbf P(\det(\frac1{\sqrt n}A_n-zI)=0\ \text{or}\ \det(\frac1{\sqrt n}B_n-zI)=0)\to0$. Together the two clauses are equivalent to the paper's (ii). The entries of $A_n,B_n$ are assumed measurable (random matrices).
-- source:
--   Tao, Vu, Random matrices: Universality of ESDs and the circular law, Ann. Probab. 38 (2010), no. 5, p. 2034 (PDF 12), Theorem 2.1 (convergence in probability version)

import Mathlib
import Definitions.Def_UnivESD_Universality_Basic
import Definitions.Def_UnivESD_Universality_Model

open MeasureTheory Filter Topology

namespace UnivESD.Universality

/-- Theorem 2.1 (replacement principle), convergence in probability, p. 2034. -/
theorem theorem_2_1 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (A B : (n : ℕ) → Ω → Matrix (Fin n) (Fin n) ℂ)
    (hA : ∀ n (i j : Fin n), Measurable fun ω => A n ω i j)
    (hB : ∀ n (i j : Fin n), Measurable fun ω => B n ω i j)
    (h1 : BoundedInProb P fun n ω =>
      (1 / (n : ℝ) ^ 2) * hsNormSq (A n ω) + (1 / (n : ℝ) ^ 2) * hsNormSq (B n ω))
    (h2 : ∀ᵐ z ∂(volume : Measure ℂ),
      TendstoInProbZero P (fun n ω => normLogDet (A n ω) z - normLogDet (B n ω) z) ∧
        Tendsto (fun n => P {ω |
          (invSqrt n • A n ω - z • (1 : Matrix (Fin n) (Fin n) ℂ)).det = 0 ∨
            (invSqrt n • B n ω - z • (1 : Matrix (Fin n) (Fin n) ℂ)).det = 0}) atTop (𝓝 0)) :
    ESDDiffTendstoInProb P A B := by sorry

end UnivESD.Universality
