-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P39_qft_quality_counts
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P39.qft_quality_counts
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T09:46:15.9257+00:00
-- url     : https://prove2.me/theorems/e5c19c45-5949-4121-9bb7-bc20f6c673c4
-- title:
--   QFT occurrence counts and modeled quality
-- statement:
--   Assign each $QFT_m$ occurrence fidelity $F_Q\in[-1,1]$ and each type-$j$ phase-swap occurrence fidelity $F_j\in[-1,1]$. With independent occurrence errors, assigned schedule duration $T\ge0$, and $T_R>0$, the modeled quality of the Fig. 7 circuit for $m,k\ge2$ is
--
--   $$q=F_Q^k\prod_{j=1}^{k-1}F_j^{k-j}\,e^{-T/T_R}.$$
--
--   For $2k$ blocks of size five, $k\ge2$, after truncation identifies every type $j\ge3$ with the same pure-swap module, write $F_5$ for the five-qubit Fourier fidelity and $F_1,F_2,F_3$ for the three remaining module fidelities. Then
--
--   $$q=F_5^{2k}F_1^{2k-1}F_2^{2k-2}F_3^{\binom{2k}{2}-4k+3}e^{-T/T_R}.$$
--
--   The fidelity product is computed from the actual circuit list. The second expression concerns the approximating circuit. Its elapsed duration is assigned independently of the deferred timing formula (25).
-- source:
--   Quantum CISC Compilation by Optimal Control and Scalable Assembly of Complex Instruction Sets beyond Two-Qubit Gates, arXiv:0712.3227v2, PDF p. 10, QFT counts and model quality, Eqs. (26)–(27)

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P39

namespace QAlgorithms.Papers.Independent.Intakethird100.P39

open scoped BigOperators

/-- PDF p.10, Eqs. (26)-(27): occurrence-count quality formulas. In the
second formula, all phase-swap types j>=3 have been replaced by the same
truncated pure-swap module. T is an assigned elapsed time, without Eq. (25). -/
theorem qft_quality_counts (Fq : ℝ) (Fc : ℕ → ℝ) (T TR : ℝ)
    (hT : 0 ≤ T) (hTR : 0 < TR)
    (hFq : Fq ∈ Set.Icc (-1) 1) (hFc : ∀ j, Fc j ∈ Set.Icc (-1) 1) :
    (∀ m k : ℕ, 2 ≤ m → 2 ≤ k →
      blockQuality Fq Fc T TR (qftAssembly m k) =
        Fq ^ k * (∏ j ∈ Finset.Icc 1 (k - 1), Fc j ^ (k - j)) *
          Real.exp (-T / TR)) ∧
    (∀ (k : ℕ) (F5 F1 F2 F3 : ℝ), 2 ≤ k →
      F5 ∈ Set.Icc (-1) 1 → F1 ∈ Set.Icc (-1) 1 →
      F2 ∈ Set.Icc (-1) 1 → F3 ∈ Set.Icc (-1) 1 →
      blockQuality F5 (fun j => if j = 1 then F1 else if j = 2 then F2 else F3)
        T TR (truncatedQftAssembly 5 (2 * k) 10) =
        F5 ^ (2 * k) * F1 ^ (2 * k - 1) * F2 ^ (2 * k - 2) *
          F3 ^ (Nat.choose (2 * k) 2 - (4 * k - 3)) * Real.exp (-T / TR)) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P39
