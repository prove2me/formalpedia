-- Prove2me | Theorems.Thm_TightQLB_Supplement_theorem_6_12
-- name    : TightQLB.Supplement.theorem_6_12
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T16:25:49.471471+00:00
-- url     : https://prove2.me/theorems/14c5ade3-a48d-44b2-a76d-6206bacd0756
-- title:
--   Theorem 6.12 — heavy-output query bounds: (57), (58), $\Theta_h(N^{1/3})$ for $h\in(h_{\mathrm{hon}},h_\star)$, and $\mathsf{Sq}_m$ reaches $h_\star$
-- statement:
--   Let $N=2^n\ge2$, $p_z=|\langle z|\phi\rangle|^2$ for a Haar-random $|\phi\rangle$ (or $|\phi\rangle=U|0^n\rangle$ for a Haar-random $U$), $B^{\mathrm{hog}}_\tau(\mathcal A)=\Pr[p_Z>\tau]$, and let $\Lambda_{s,q}$ be as in Theorem 5.6.
--
--   1. An algorithm given $s$ copies and making at most $q$ queries to the canonical oracle, and an algorithm with Haar-random unitary access making at most $q$ queries without supplied copies, satisfy respectively
--   $$
--   B^{\mathrm{hog}}_{\theta_N}(\mathcal A)\le\beta^{\mathrm{hog}}_N+\Lambda_{s,q},\qquad B^{\mathrm{hog}}_{\theta_N}(\mathcal A)\le\beta^{\mathrm{hog}}_N+\Lambda_{0,2q}+\frac{5q+2}{\sqrt N}.
--   $$
--   2. For either threshold $\tau=\theta_N$ or $\tau=\hat\theta_N$ and every fixed $h\in(h_{\mathrm{hon}},h_\star)$, achieving $B^{\mathrm{hog}}_\tau(\mathcal A)\ge h$ without supplied copies has query complexity $\Theta_h(N^{1/3})$ for either form of Haar access: there are $c_h,C_h>0$ and $N_h$ such that for $N\ge N_h$ every such algorithm makes at least $c_hN^{1/3}$ queries and some algorithm with at most $C_hN^{1/3}$ queries achieves it.
--   3. For $N\ge64$, $\mathsf{Sq}_m$ with $m=\lceil N^{1/3}\rceil$ makes at most $3N^{1/3}$ queries, and its heavy probability tends to $h_\star$ as $N\to\infty$ under both thresholds.
--
--   Here $\theta_N=1-2^{-1/(N-1)}$, $\hat\theta_N$ is the empirical median, $\beta^{\mathrm{hog}}_N=(1+(N-1)\theta_N)/2$, $h_{\mathrm{hon}}=(1+\ln2)/2$ and $h_\star=(2+2\ln2+(\ln2)^2)/4$.
--
--   **Formalization Note** For unitary access the upper-bound algorithm is fixed before the Haar law. The limit in (iii) holds for every choice of the integers $\ell$ of Definition 6.1 and for both forms of Haar access.
--
--   Differences from the source:
--   - reading: Θ_h(N^{1/3}) query complexity → ∃ c_h, C_h > 0 and N_h such that for all N = 2^n ≥ N_h: every algorithm without copies reaching B^hog_τ ≥ h makes ≥ c_h N^{1/3} queries, and some algorithm with ≤ C_h N^{1/3} queries reaches it; for both thresholds and both forms of Haar access; reason: the standard meaning of Θ_h for a fixed h
--   - reading: "its heavy probability tends to h⋆" → Tendsto as n → ∞, for every sequence of admissible ℓ_n, for the Haar law and for U|0ⁿ⟩ under every sequence of Haar laws on U(n); reason: limit of the stated quantity as N → ∞
--   - reading: algorithms "given s copies", "with Haar-random unitary access", "without supplied copies" → CopyExperiment, UnitaryExperiment and the base mission's Experiment with the canonical oracle (channel form); reason: the experiments of Definition 3.1 and Kretschmer's model, as in Theorems 5.6 and 5.25
--   - generalization: the theorems about the score alone, "the special case in which Eve's register is trivial" (p. 15) → every finite Eve register E and every joint initial state; reason: E = Unit is the source's statement; nothing acts on E, so the score does not depend on it
--   - encoding: θ̂_N = (p_(N/2) + p_(N/2+1))/2, values sorted increasingly → orderStat p j = inf{t : #{z : p_z ≤ t} ≥ j}; reason: the j-th smallest value with multiplicity
--   - encoding: the absolute constant c0 of Theorem 5.21 in Λ_{s,q} → c0 = 54; reason: "The proof gives c0 = 54" (p. 44, PDF p. 47)
--   - encoding: N = 2^n, N^{1/3}, N^{−1/3}, √N → (2 : ℝ)^n with Real.rpow and Real.sqrt; reason: Lean convention; same values
-- source:
--   Bhateja, Esmaili, Mantri, Tight Query Lower Bounds for Quantum Sampling, with an Application to Certified Randomness, arXiv:2610.06721 (version of sha256 00a999f1…), Theorem 6.12, p. 56 (PDF p. 59); Eqs. (54)–(56), pp. 55–56 (PDF pp. 58–59)

import Mathlib
import Definitions.Def_TightQLB_Supplement_Heavy
open QAlgorithms MeasureTheory Filter Topology

set_option autoImplicit false

namespace TightQLB.Supplement

/-- **Theorem 6.12 (Heavy-output query bounds)**, p.56 (PDF p.59).

Bhateja, Esmaili, Mantri, *Tight Query Lower Bounds for Quantum Sampling, with an Application to
Certified Randomness*, arXiv:2610.06721 (version of sha256 00a999f1…).

"Let `Λ_{s,q}` be as in Theorem 5.6. (i) An algorithm given `s` copies and making at most `q`
queries to the canonical oracle satisfies the first bound below, and an algorithm with Haar-random
unitary access making at most `q` queries, without supplied copies, satisfies the second:
`B^hog_{θ_N}(A) ≤ β^hog_N + Λ_{s,q}`, (57) `B^hog_{θ_N}(A) ≤ β^hog_N + Λ_{0,2q} + (5q + 2)/√N`. (58)
(ii) For either threshold `τ = θ_N` or `τ = θ̂_N`, and every fixed `h ∈ (h_hon, h⋆)`, achieving
`B^hog_τ(A) ≥ h` without supplied copies has query complexity `Θ_h(N^{1/3})` for either form of
Haar access. (iii) For `N ≥ 64`, `Sq_m` with `m = ⌈N^{1/3}⌉` makes at most `3N^{1/3}` queries and its
heavy probability tends to `h⋆` under both threshold conventions."

**Formalization Note.**
* Algorithms: `CopyExperiment` (canonical oracle, `s` copies), the published `Experiment` with the
  canonical oracle (no copies), `UnitaryExperiment` (unitary access) with Haar law `μ`.
* (ii) `Θ_h(N^{1/3})`: for each `h` there are `c_h, C_h > 0` and `N_h` such that for every
  `N = 2^n ≥ N_h`, every algorithm without copies with `B^hog_τ ≥ h` makes at least `c_h N^{1/3}`
  queries, and some algorithm with at most `C_h N^{1/3}` queries has `B^hog_τ ≥ h` — for both
  thresholds and both forms of Haar access. For unitary access the algorithm is fixed before `μ`.
* (iii) The limit is as `n → ∞`, for every choice of the integers `ℓ_n` of Definition 6.1
  (`κ₂ = 2`), for the Haar law and for the law of `U|0ⁿ⟩` under every sequence of Haar laws.
* Thresholds are `thetaFix` (`θ_N`) and `thetaHat` (`θ̂_N`); `n ≥ 1` in (i) (`N ≥ 2`). -/
theorem theorem_6_12 :
    (∀ {n : ℕ}, 1 ≤ n → ∀ {q s : ℕ} {W E : Type} [Fintype W] [DecidableEq W] [Fintype E]
      [DecidableEq E], ∀ A : CopyExperiment n q s W E,
        A.heavy (thetaFix n) ≤ betaHog n + Lam n s q) ∧
    (∀ {n : ℕ}, 1 ≤ n → ∀ {q : ℕ} {W E : Type} [Fintype W] [DecidableEq W] [Fintype E]
      [DecidableEq E] (μ : Measure (Qubits n → Qubits n → ℂ)), IsHaarUnitaryLaw μ →
      ∀ A : UnitaryExperiment n q W E,
        A.heavy μ (thetaFix n) ≤ betaHog n + Lam n 0 (2 * q) + (5 * q + 2) / Real.sqrt ((2 : ℝ) ^ n)) ∧
    (∀ τ : (n : ℕ) → (Qubits n → ℝ) → ℝ, (τ = thetaFix ∨ τ = thetaHat) →
      ∀ h : ℝ, hHon < h → h < hStar →
        ∃ c C N₀ : ℝ, 0 < c ∧ 0 < C ∧ ∀ n : ℕ, N₀ ≤ (2 : ℝ) ^ n →
          (∀ (q : ℕ) (W E : Type) [Fintype W] [DecidableEq W] [Fintype E] [DecidableEq E]
            (A : Experiment n q (Option (Qubits n)) W E), h ≤ haarHeavy A (τ n) →
              c * ((2 : ℝ) ^ n) ^ (1 / 3 : ℝ) ≤ q) ∧
          (∀ (q : ℕ) (W E : Type) [Fintype W] [DecidableEq W] [Fintype E] [DecidableEq E]
            (μ : Measure (Qubits n → Qubits n → ℂ)), IsHaarUnitaryLaw μ →
            ∀ A : UnitaryExperiment n q W E, h ≤ A.heavy μ (τ n) →
              c * ((2 : ℝ) ^ n) ^ (1 / 3 : ℝ) ≤ q) ∧
          (∃ (q : ℕ) (W E : Type) (_ : Fintype W) (_ : DecidableEq W) (_ : Fintype E)
            (_ : DecidableEq E) (A : Experiment n q (Option (Qubits n)) W E),
              (q : ℝ) ≤ C * ((2 : ℝ) ^ n) ^ (1 / 3 : ℝ) ∧ h ≤ haarHeavy A (τ n)) ∧
          (∃ (q : ℕ) (W E : Type) (_ : Fintype W) (_ : DecidableEq W) (_ : Fintype E)
            (_ : DecidableEq E) (A : UnitaryExperiment n q W E),
              (q : ℝ) ≤ C * ((2 : ℝ) ^ n) ^ (1 / 3 : ℝ) ∧
              ∀ μ : Measure (Qubits n → Qubits n → ℂ), IsHaarUnitaryLaw μ →
                h ≤ A.heavy μ (τ n))) ∧
    (∀ n : ℕ, 64 ≤ (2 : ℝ) ^ n → ∀ ℓ : ℕ, IsSqSteps n 2 ⌈((2 : ℝ) ^ n) ^ (1 / 3 : ℝ)⌉₊ ℓ →
      (sqQueries ⌈((2 : ℝ) ^ n) ^ (1 / 3 : ℝ)⌉₊ ℓ : ℝ) ≤ 3 * ((2 : ℝ) ^ n) ^ (1 / 3 : ℝ)) ∧
    (∀ ℓ : ℕ → ℕ, (∀ n, IsSqSteps n 2 ⌈((2 : ℝ) ^ n) ^ (1 / 3 : ℝ)⌉₊ (ℓ n)) →
      ∀ τ : (n : ℕ) → (Qubits n → ℝ) → ℝ, (τ = thetaFix ∨ τ = thetaHat) →
        Tendsto (fun n => sqHeavy (haar n) ⌈((2 : ℝ) ^ n) ^ (1 / 3 : ℝ)⌉₊ (ℓ n) (τ n)) atTop
            (𝓝 hStar) ∧
        ∀ μ : (n : ℕ) → Measure (Qubits n → Qubits n → ℂ), (∀ n, IsHaarUnitaryLaw (μ n)) →
          Tendsto (fun n => sqHeavy (unitaryLaw (μ n)) ⌈((2 : ℝ) ^ n) ^ (1 / 3 : ℝ)⌉₊ (ℓ n) (τ n))
            atTop (𝓝 hStar)) := by sorry

end TightQLB.Supplement
