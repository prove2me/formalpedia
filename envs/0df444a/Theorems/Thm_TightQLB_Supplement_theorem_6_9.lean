-- Prove2me | Theorems.Thm_TightQLB_Supplement_theorem_6_9
-- name    : TightQLB.Supplement.theorem_6_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T16:24:20.544906+00:00
-- url     : https://prove2.me/theorems/44fd1b41-c257-48a7-808f-e6e7cdbcfa3b
-- title:
--   Theorem 6.9 — scores of the squaring algorithm: $O(N^{1/3})$ queries, $\mathrm{TV}=O(N^{-1/3})$, score $\ge5-O(N^{-1/6})$ (Fourier), $\ge3-O(N^{-1/6})$ (Haar)
-- statement:
--   Let $N=2^n\ge64$ and $m=\lceil N^{1/3}\rceil$. Then the squaring algorithm $\mathsf{Sq}_m$:
--
--   1. makes $O(N^{1/3})$ queries;
--   2. has output distribution with $\mathbb E_\omega\mathrm{TV}(a_\omega,r_{p_\omega})=O(N^{-1/3})$;
--   3. has expected score $\mathbb E_\omega\sum_za_\omega(z)Np_\omega(z)$ at least $5-O(N^{-1/6})$ in the Fourier ensemble and at least $3-O(N^{-1/6})$ for either form of Haar access.
--
--   Each $O(\cdot)$ is a single absolute constant $C$, valid for all $N\ge64$, all three ensembles and every admissible number of amplification steps.
--
--   Since the ideal scores are $3-2/N$ (Fourier) and $2N/(N+1)$ (Haar), this shows that $O(N^{1/3})$ queries suffice to beat honest sampling by a constant, matching the lower bounds of Theorems 4.5, 5.6 and 5.25.
--
--   Differences from the source:
--   - reading: each O(·) in (i)–(iii) → one absolute constant C, chosen before N ≥ 64, the ensemble and ℓ; reason: O-notation for an absolute bound valid for all N ≥ 64
--   - encoding: the output distribution a_ω of Sq_m in the Fourier ensemble, with the canonical oracle, and with unitary access, and E_ω → sqOut computed from the four steps of Definition 6.1 for the prepared state ψ_ω, and integrals over the law ν of ψ_ω (IsEnsemble: Fourier with κ2 = 3, Haar and U|0ⁿ⟩ with κ2 = 2); reason: §6.1: the queries implement exactly the preparation of ψ_ω and the reflection about it, and a_ω depends on the oracle only through ψ_ω
--   - encoding: "ℓ a nonnegative integer nearest to π/(4ϑ0) − 1/2" → every ℓ with IsNearestNat (π/(4ϑ0) − 1/2) ℓ; reason: the theorem holds for each such choice
--   - encoding: N = 2^n, N^{1/3}, N^{−1/3}, √N → (2 : ℝ)^n with Real.rpow and Real.sqrt; reason: Lean convention; same values
-- source:
--   Bhateja, Esmaili, Mantri, Tight Query Lower Bounds for Quantum Sampling, with an Application to Certified Randomness, arXiv:2610.06721 (version of sha256 00a999f1…), Theorem 6.9, p. 53 (PDF p. 56)

import Mathlib
import Definitions.Def_TightQLB_Supplement_Squaring
open QAlgorithms MeasureTheory

set_option autoImplicit false

namespace TightQLB.Supplement

/-- **Theorem 6.9 (Scores of the squaring algorithm)**, p.53 (PDF p.56).

Bhateja, Esmaili, Mantri, *Tight Query Lower Bounds for Quantum Sampling, with an Application to
Certified Randomness*, arXiv:2610.06721 (version of sha256 00a999f1…).

"Let `N ≥ 64` and `m = ⌈N^{1/3}⌉`. Then the squaring algorithm has the following properties.
(i) It makes `O(N^{1/3})` queries. (ii) Its output distribution satisfies
`E_ω TV(a_ω, r_{p_ω}) = O(N^{−1/3})`. (iii) Its expected score is at least `5 − O(N^{−1/6})` in the
Fourier ensemble and at least `3 − O(N^{−1/6})` for either form of Haar access."

**Formalization Note.**
* Each `O(·)` is one absolute constant `C`, chosen before `N`, the ensemble and `ℓ`.
* The ensembles are those of `IsEnsemble` (Fourier: `κ₂ = 3`; canonical oracle and unitary access:
  `κ₂ = 2`); `ℓ` is any integer of Definition 6.1 for that `κ₂`. The expected score of `Sq_m` is
  `sqScore ν m ℓ = E_ω Σ_z a_ω(z) N p_ω(z)`. -/
theorem theorem_6_9 :
    ∃ C : ℝ, ∀ n : ℕ, 64 ≤ (2 : ℝ) ^ n → ∀ (ν : Measure (EuclideanSpace ℂ (Qubits n))) (κ₂ : ℝ),
      IsEnsemble n ν κ₂ → ∀ ℓ : ℕ, IsSqSteps n κ₂ ⌈((2 : ℝ) ^ n) ^ (1 / 3 : ℝ)⌉₊ ℓ →
        (sqQueries ⌈((2 : ℝ) ^ n) ^ (1 / 3 : ℝ)⌉₊ ℓ : ℝ) ≤ C * ((2 : ℝ) ^ n) ^ (1 / 3 : ℝ) ∧
        sqTV ν ⌈((2 : ℝ) ^ n) ^ (1 / 3 : ℝ)⌉₊ ℓ ≤ C * ((2 : ℝ) ^ n) ^ (-(1 / 3 : ℝ)) ∧
        (κ₂ = 3 → 5 - C * ((2 : ℝ) ^ n) ^ (-(1 / 6 : ℝ)) ≤
          sqScore ν ⌈((2 : ℝ) ^ n) ^ (1 / 3 : ℝ)⌉₊ ℓ) ∧
        (κ₂ = 2 → 3 - C * ((2 : ℝ) ^ n) ^ (-(1 / 6 : ℝ)) ≤
          sqScore ν ⌈((2 : ℝ) ^ n) ^ (1 / 3 : ℝ)⌉₊ ℓ) := by sorry

end TightQLB.Supplement
