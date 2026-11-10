-- Prove2me | Theorems.Thm_QPSpinProfile_theorem_1_2
-- name    : QPSpinProfile.theorem_1_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T03:28:09.991919+00:00
-- url     : https://prove2.me/theorems/b8b23edc-a093-4d82-a12b-9c0d323f26ba
-- title:
--   Theorem 1.2: local-profile complexity principle (both parts)
-- statement:
--   Let $(\mathcal C_n)$ be classes of $n$-qubit states. Let $a_{n,p},b_{n,p}\ge0$ and $B_{n,p}\ge1$ satisfy, for integers $n\ge p\ge2$ and $0<\varepsilon<1$,
--   $$
--   \log N\big(\varepsilon,F_{n,p}(\mathcal C_n),\|\cdot\|_{n,p}\big)\le a_{n,p}+b_{n,p}\log\frac{B_{n,p}}{\varepsilon},
--   $$
--   and let $\Gamma_{n,p}=a_{n,p}+b_{n,p}\log(eB_{n,p}n)$ be the effective profile complexity.
--
--   1. **Quadratic ground-state separation.** For every $L\ge0$ there is $p_0$ such that for every fixed $p\ge p_0$ there is $c_{p,L}>0$ with the following property: whenever $\limsup_{n\to\infty}\Gamma_{n,p}/n^2\le L$,
--   $$
--   \mathbb P\big(\Delta^{\mathrm{opt}}_{n,p}(\mathcal C_n)\ge c_{p,L}\sqrt n\big)\longrightarrow1 .
--   $$
--   2. **Subquadratic benchmark comparison.** Let $(\mathcal B_n)$ be a conditioning benchmark for $(\mathcal C_n)$ (Definition 1.1). For every fixed $p\ge2$, if $\Gamma_{n,p}=o(n^2)$, then
--   $$
--   \frac{\Delta^{\mathrm{ref}}_{n,p}(\mathcal C_n;\mathcal B_n)}{\sqrt n}\longrightarrow0
--   $$
--   in $L^1$ and in probability as $n\to\infty$.
--
--   Part (i) says that, for large fixed $p$, a class of at most quadratic profile complexity cannot approach the ground-state energy on its natural $\sqrt n$ scale; part (ii) says that subquadratic profile complexity gives no leading-order energy advantage over any conditioning benchmark, in particular over product states. Every application in the paper (circuit size, depth–width, entanglement depth, MPS, magic, Clifford+T) is this theorem plus an entropy bound for the class.
--
--   Differences from the source:
--   - encoding: Pauli strings $P^a_I$ and independent standard Gaussian coefficients $g_P$ → words $w : \mathrm{Fin}\,n \to \mathrm{Fin}\,4$ with exactly $p$ non-identity letters; the disorder is a vector $g \in \mathbb R^{\mathcal P_{n,p}}$ with law $\bigotimes_P N(0,1)$; reason: bijection with the pairs $(I, a)$; same model
--   - encoding: standing assumption (p.3): all state classes are nonempty → explicit hypotheses that each class is nonempty and consists of density operators; reason: the paper's standing assumption made explicit; it also keeps the real suprema $E_{n,p}$ meaningful
--   - reading: "for some $c_{p,L}>0$" → $c$ chosen after $p$ and before the class sequence and the entropy parameters; reason: the subscript and the proof (pp.27–28) make $c$ depend only on $p$ and $L$; this is the stronger of the two readings
--   - encoding: $\log N\le a_{n,p}+b_{n,p}\log(B_{n,p}/\varepsilon)$ → $N$ finite and $\log N\le a_{n,p}+b_{n,p}\log(B_{n,p}/\varepsilon)$, for $n\ge p$ and $0<\varepsilon<1$; reason: an infinite $N$ makes the printed bound false
--   - encoding: $\limsup_n\Gamma_{n,p}/n^2\le L$ → for every $\delta>0$, eventually $\Gamma_{n,p}/n^2\le L+\delta$; reason: the definition of the lim sup, avoiding Mathlib's junk value of `limsup` on unbounded real sequences
--   - encoding: $\Gamma_{n,p}=o(n^2)$ → $\Gamma_{n,p}/n^2\to0$; reason: the definition of $o(n^2)$
--   - encoding: convergence to $0$ in $L^1$ and in probability → the lower Lebesgue integral of $\Delta^{\mathrm{ref}}/\sqrt n$ tends to $0$, and $\mathbb P(\Delta^{\mathrm{ref}}/\sqrt n\ge\varepsilon)\to0$ for every $\varepsilon>0$; reason: $\Delta^{\mathrm{ref}}\ge0$, so these are exactly the two modes of convergence
--   - encoding: $\log(eB_{n,p}n)$ → `Real.log (exp 1 * B n * n)`; reason: equal
-- source:
--   Al-Ghattas, Gamarnik, Kiani, Beyond light cones: State preparation complexity in quantum spin glasses, arXiv:2610.02166 (held version, sha256 a0a1ec89…), Theorem 1.2, p.4–5 (PDF p.7–8)

import Mathlib
import Definitions.Def_WildeQIT_IsDensityOperator
import Definitions.Def_QPSpinProfile_profile
import Definitions.Def_QPSpinProfile_coverNum
import Definitions.Def_QPSpinProfile_maxEnergy
import Definitions.Def_QPSpinProfile_IsConditioningBenchmark

namespace QPSpinProfile

open MeasureTheory Filter Topology

/-- **Theorem 1.2 (Local-profile complexity principle)** (Al-Ghattas, Gamarnik, Kiani, *Beyond light cones: State preparation complexity in quantum spin glasses*, arXiv:2610.02166 (held version, sha256 a0a1ec89…), p.4–5, PDF p.7–8).
Let `a_{n,p}, b_{n,p} ≥ 0`, `B_{n,p} ≥ 1` satisfy, for `n ≥ p ≥ 2` and `0 < ε < 1`,
`log N(ε, F_{n,p}(C_n), ‖·‖_{n,p}) ≤ a_{n,p} + b_{n,p} log(B_{n,p}/ε)`, and let
`Γ_{n,p} := a_{n,p} + b_{n,p} log(e B_{n,p} n)`.
(i) For every `L ≥ 0` and every sufficiently large fixed `p` depending only on `L`,
`lim sup_n Γ_{n,p}/n² ≤ L` implies, for some `c_{p,L} > 0`, `P(Δ^opt_{n,p}(C_n) ≥ c_{p,L}√n) → 1`.
(ii) If `B_n` is a conditioning benchmark for `C_n` (Definition 1.1), then for every fixed
`p ≥ 2`, `Γ_{n,p} = o(n²)` implies `Δ^ref_{n,p}(C_n; B_n)/√n → 0` in `L¹` and in probability.

**Formalization Note** In (i), `p₀` depends only on `L` and `c_{p,L}` only on `p` and `L`: both are
chosen before the class and the entropy parameters. "`log N ≤ …`" is "`N` finite and
`log N ≤ …`". `lim sup_n x_n ≤ L` is `∀ δ > 0, eventually x_n ≤ L + δ`; `Γ = o(n²)` is
`Γ_{n,p}/n² → 0`. Convergence in `L¹` of the nonnegative `Δ^ref/√n` is convergence of its lower
Lebesgue integral to `0`; in probability is `P(Δ^ref/√n ≥ ε) → 0` for every `ε > 0`. Classes are
nonempty sets of states (the paper's standing assumption, p.3). -/
theorem theorem_1_2 :
    (∀ L : ℝ, 0 ≤ L → ∃ p₀ : ℕ, ∀ p : ℕ, p₀ ≤ p → ∃ c : ℝ, 0 < c ∧
      ∀ (Cl : (n : ℕ) → Set (Matrix (Qubits n) (Qubits n) ℂ)) (a b B : ℕ → ℝ),
        (∀ n, (Cl n).Nonempty) → (∀ n, ∀ ρ ∈ Cl n, WildeQIT.IsDensityOperator ρ) →
        (∀ n : ℕ, p ≤ n → 0 ≤ a n ∧ 0 ≤ b n ∧ 1 ≤ B n) →
        (∀ n : ℕ, p ≤ n → ∀ ε : ℝ, 0 < ε → ε < 1 →
          coverNum ε (profileClass n p (Cl n)) ≠ ⊤ ∧
          Real.log ((coverNum ε (profileClass n p (Cl n))).toNat : ℝ)
            ≤ a n + b n * Real.log (B n / ε)) →
        (∀ δ : ℝ, 0 < δ → ∀ᶠ n : ℕ in atTop,
          (a n + b n * Real.log (Real.exp 1 * B n * n)) / (n : ℝ) ^ 2 ≤ L + δ) →
        Tendsto (fun n : ℕ => gaussMeasure n p
          {g | c * Real.sqrt n ≤ deltaOpt n p (Cl n) g}) atTop (𝓝 1)) ∧
    (∀ (Cl Bl : (n : ℕ) → Set (Matrix (Qubits n) (Qubits n) ℂ)),
      (∀ n, (Cl n).Nonempty) → (∀ n, ∀ ρ ∈ Cl n, WildeQIT.IsDensityOperator ρ) →
      (∀ n, (Bl n).Nonempty) → (∀ n, ∀ σ ∈ Bl n, WildeQIT.IsDensityOperator σ) →
      IsConditioningBenchmark Bl Cl →
      ∀ p : ℕ, 2 ≤ p → ∀ (a b B : ℕ → ℝ),
        (∀ n : ℕ, p ≤ n → 0 ≤ a n ∧ 0 ≤ b n ∧ 1 ≤ B n) →
        (∀ n : ℕ, p ≤ n → ∀ ε : ℝ, 0 < ε → ε < 1 →
          coverNum ε (profileClass n p (Cl n)) ≠ ⊤ ∧
          Real.log ((coverNum ε (profileClass n p (Cl n))).toNat : ℝ)
            ≤ a n + b n * Real.log (B n / ε)) →
        Tendsto (fun n : ℕ => (a n + b n * Real.log (Real.exp 1 * B n * n)) / (n : ℝ) ^ 2)
          atTop (𝓝 0) →
        Tendsto (fun n : ℕ => ∫⁻ g, ENNReal.ofReal (deltaRef n p (Cl n) (Bl n) g / Real.sqrt n)
          ∂(gaussMeasure n p)) atTop (𝓝 0) ∧
        ∀ ε : ℝ, 0 < ε → Tendsto (fun n : ℕ => gaussMeasure n p
          {g | ε ≤ deltaRef n p (Cl n) (Bl n) g / Real.sqrt n}) atTop (𝓝 0)) := by sorry

end QPSpinProfile
