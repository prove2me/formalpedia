-- Prove2me | Theorems.Thm_TightQLB_Supplement_theorem_6_6
-- name    : TightQLB.Supplement.theorem_6_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T16:23:23.502366+00:00
-- url     : https://prove2.me/theorems/93dd4559-b67d-4fd4-8d0b-061a6f814922
-- title:
--   Theorem 6.6 — output distribution of the squaring algorithm: the bound (52) on $\mathbb E_\omega\mathrm{TV}(a_\omega,r_{p_\omega})$, and (53) for $m=\lceil N^{1/3}\rceil$
-- statement:
--   Let $N=2^n$, and work in one of the three ensembles: Fourier ($\kappa_2=3$), Haar with the canonical oracle, or Haar-random unitary access ($\kappa_2=2$). Let $m\ge1$ with $\kappa_2m/N\le1/4$, and let $a_\omega(z)=\Pr[Z=z\mid\omega]$ be the output distribution of the squaring algorithm $\mathsf{Sq}_m$. Then
--
--   $$
--   \mathbb E_\omega\mathrm{TV}(a_\omega,r_{p_\omega})\le\frac1m\,\mathbb E_\omega\Big[\frac{M_3}{M_2^2}\Big]+\binom m2\frac{\mathbb EM_2}{N}+\frac{18}{\kappa_2^2}\Big(\frac{\mathbb EM_3}{m}+\mathbb E(M_2-\kappa_2)^2\Big)+\frac{3\kappa_2m}{N}. \tag{52}
--   $$
--
--   In particular, if $N\ge64$ and $m=\lceil N^{1/3}\rceil$, then $\mathsf{Sq}_m$ makes at most $3N^{1/3}$ queries and
--
--   $$
--   \mathbb E_\omega\mathrm{TV}(a_\omega,r_{p_\omega})\le\begin{cases}40\,N^{-1/3}&\text{in the Haar ensemble},\\ 60\,N^{-1/3}&\text{in the Fourier ensemble}.\end{cases}\tag{53}
--   $$
--
--   Here $M_j=N^{j-1}\sum_zp_z^j$ and $r_p(z)=p_z^2/\sum_yp_y^2$ is the collision distribution. The four terms of (52) are the bias of the averaged stored set, a repeated stored outcome, the amplification error, and the rounding of the number of steps.
--
--   Differences from the source:
--   - encoding: the output distribution a_ω of Sq_m in the Fourier ensemble, with the canonical oracle, and with unitary access, and E_ω → sqOut computed from the four steps of Definition 6.1 for the prepared state ψ_ω, and integrals over the law ν of ψ_ω (IsEnsemble: Fourier with κ2 = 3, Haar and U|0ⁿ⟩ with κ2 = 2); reason: §6.1: the queries implement exactly the preparation of ψ_ω and the reflection about it, and a_ω depends on the oracle only through ψ_ω
--   - encoding: "ℓ a nonnegative integer nearest to π/(4ϑ0) − 1/2" → every ℓ with IsNearestNat (π/(4ϑ0) − 1/2) ℓ; reason: the theorem holds for each such choice
--   - reading: (53) "in the Haar ensemble" → both forms of Haar access (canonical oracle and unitary access, κ2 = 2); reason: §6 treats the three forms together, and U|0ⁿ⟩ is Haar-distributed, so both give the same quantity
--   - encoding: N = 2^n, N^{1/3}, N^{−1/3}, √N → (2 : ℝ)^n with Real.rpow and Real.sqrt; reason: Lean convention; same values
-- source:
--   Bhateja, Esmaili, Mantri, Tight Query Lower Bounds for Quantum Sampling, with an Application to Certified Randomness, arXiv:2610.06721 (version of sha256 00a999f1…), Theorem 6.6, p. 51 (PDF p. 54)

import Mathlib
import Definitions.Def_TightQLB_Supplement_Squaring
open QAlgorithms MeasureTheory

set_option autoImplicit false

namespace TightQLB.Supplement

/-- **Theorem 6.6 (Output distribution of the squaring algorithm)**, p.51 (PDF p.54).

Bhateja, Esmaili, Mantri, *Tight Query Lower Bounds for Quantum Sampling, with an Application to
Certified Randomness*, arXiv:2610.06721 (version of sha256 00a999f1…).

"Let `m ≥ 1` satisfy `κ₂m/N ≤ 1/4`, and for each oracle `ω` let `a_ω(z) = Pr[Z = z | ω]` be the
output distribution of `Sq_m`. Then
`E_ω TV(a_ω, r_{p_ω}) ≤ (1/m) E_ω[M₃/M₂²] + (m choose 2) EM₂/N + (18/κ₂²)(EM₃/m + E(M₂ − κ₂)²) + 3κ₂m/N`.
(52) In particular, if `N ≥ 64` and `m = ⌈N^{1/3}⌉`, then `Sq_m` makes at most `3N^{1/3}` queries and
`E_ω TV(a_ω, r_{p_ω}) ≤ 40 N^{−1/3}` in the Haar ensemble, `60 N^{−1/3}` in the Fourier ensemble.
(53)"

**Formalization Note.**
* The ensemble is one of the three forms of access of §6.1 (`IsEnsemble n ν κ₂`: Fourier with
  `κ₂ = 3`, canonical oracle or unitary access with `κ₂ = 2`); `E_ω` is `∫ · ∂ν` over the prepared
  state `ψ = |ψ_ω⟩`, `p_ω = |ψ|²` (`pOf`), `M_j` is `moment j`, `r_p` is `collision`.
* `ℓ` is any nonnegative integer nearest to `π/(4ϑ₀) − 1/2` (`IsSqSteps`), as in Definition 6.1;
  `a_ω` is `sqOut m ℓ ψ`, `E_ω TV(a_ω, r_{p_ω})` is `sqTV ν m ℓ`.
* The query count of `Sq_m` is `m + 1 + 2ℓ` (`sqQueries`). "The Haar ensemble" covers both forms
  of Haar access (`κ₂ = 2`). `n ≥ 1` (§3.1). -/
theorem theorem_6_6 {n : ℕ} (hn : 1 ≤ n) (ν : Measure (EuclideanSpace ℂ (Qubits n))) (κ₂ : ℝ)
    (hν : IsEnsemble n ν κ₂) :
    (∀ m ℓ : ℕ, 1 ≤ m → κ₂ * m / (2 : ℝ) ^ n ≤ 1 / 4 → IsSqSteps n κ₂ m ℓ →
      sqTV ν m ℓ ≤
        1 / (m : ℝ) * ∫ ψ, moment 3 (pOf ψ) / moment 2 (pOf ψ) ^ 2 ∂ν +
        (m.choose 2 : ℝ) * (∫ ψ, moment 2 (pOf ψ) ∂ν) / (2 : ℝ) ^ n +
        18 / κ₂ ^ 2 * ((∫ ψ, moment 3 (pOf ψ) ∂ν) / m + ∫ ψ, (moment 2 (pOf ψ) - κ₂) ^ 2 ∂ν) +
        3 * κ₂ * m / (2 : ℝ) ^ n) ∧
    (64 ≤ (2 : ℝ) ^ n → ∀ ℓ : ℕ, IsSqSteps n κ₂ ⌈((2 : ℝ) ^ n) ^ (1 / 3 : ℝ)⌉₊ ℓ →
      (sqQueries ⌈((2 : ℝ) ^ n) ^ (1 / 3 : ℝ)⌉₊ ℓ : ℝ) ≤ 3 * ((2 : ℝ) ^ n) ^ (1 / 3 : ℝ) ∧
      (κ₂ = 2 → sqTV ν ⌈((2 : ℝ) ^ n) ^ (1 / 3 : ℝ)⌉₊ ℓ ≤ 40 * ((2 : ℝ) ^ n) ^ (-(1 / 3 : ℝ))) ∧
      (κ₂ = 3 → sqTV ν ⌈((2 : ℝ) ^ n) ^ (1 / 3 : ℝ)⌉₊ ℓ ≤ 60 * ((2 : ℝ) ^ n) ^ (-(1 / 3 : ℝ)))) := by sorry

end TightQLB.Supplement
