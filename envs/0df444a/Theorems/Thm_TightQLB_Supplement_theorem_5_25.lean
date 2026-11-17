-- Prove2me | Theorems.Thm_TightQLB_Supplement_theorem_5_25
-- name    : TightQLB.Supplement.theorem_5_25
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T16:22:13.588167+00:00
-- url     : https://prove2.me/theorems/da4730fb-188b-4cf1-b3ea-8501e5bd6bc6
-- title:
--   Theorem 5.25 — Haar lower bound for unitary access: $B(\mathcal A)\le\beta_N+2\sqrt2\Lambda_{0,2q}+72\Lambda_{0,2q}^2+(5q+2)H_N/\sqrt N$, and $q\ge c_3\varepsilon^{2/3}N^{1/3}$
-- statement:
--   Let $N=2^n$ with $n\ge1$, and let an algorithm make $q$ queries to a Haar-random unitary $U$ on $\mathbb C^N$, with inverse and controlled access; the scored state is $|\phi\rangle=U|0^n\rangle$. Then
--
--   $$
--   B(\mathcal A)\le\beta_N+2\sqrt2\,\Lambda_{0,2q}+72\,\Lambda_{0,2q}^2+\frac{(5q+2)H_N}{\sqrt N},
--   $$
--
--   with $\Lambda_{s,q}$ as in Theorem 5.6 ($c_0=54$) and $H_N=\sum_{j=1}^N1/j$. Consequently there is an absolute constant $c_3>0$ such that for every $0<\varepsilon\le1$ and every $N$ with
--
--   $$
--   (5N^{1/3}+2)(\ln N+1)\le\varepsilon\sqrt N/2,
--   $$
--
--   every such algorithm with $B(\mathcal A)\ge2+\varepsilon$ makes at least $c_3\,\varepsilon^{2/3}N^{1/3}$ queries.
--
--   Together with Theorem 6.9 this shows that $\Theta(N^{1/3})$ queries are necessary and sufficient to beat the ideal score by a constant with unitary access.
--
--   **Formalization Note** An algorithm is an oracle-independent initial state, CPTP rounds, one query of a fixed kind ($U$, $U^\dagger$, controlled $U$ or controlled $U^\dagger$) per slot and a POVM. The Haar law on $U(N)$ is any left-invariant probability measure concentrated on unitaries. The constant $c_3$ is chosen before $n$, $\varepsilon$ and the algorithm.
--
--   Differences from the source:
--   - reading: an algorithm making q queries to a Haar-random unitary, with inverse and controlled access ("the models of Kretschmer [Kre21]", p. 14) → UnitaryExperiment: an oracle-independent density matrix, q + 1 CPTP rounds, a query of a fixed kind (U, U†, cU, cU†) in each slot, and a POVM; reason: this is Kretschmer's model, a fixed sequence of queries interleaved with oracle-independent operations, in the channel form of the base mission
--   - encoding: the Haar measure on U(N) → every probability measure on matrices concentrated on unitaries and invariant under left multiplication by unitaries; reason: the Haar probability measure of a compact group is the unique such measure
--   - reading: "a score of 2 + ε requires at least c3 ε^{2/3} N^{1/3} queries", for every N with the displayed condition → for N = 2^n, n ≥ 1, B(A) ≥ 2 + ε implies q ≥ c3 ε^{2/3} N^{1/3}, with c3 chosen before n, ε and the algorithm; reason: N = 2^n throughout (§3.1), and the constant is absolute
--   - generalization: the theorems about the score alone, "the special case in which Eve's register is trivial" (p. 15) → every finite Eve register E and every joint initial state; reason: E = Unit is the source's statement; nothing acts on E, so the score does not depend on it
--   - encoding: the absolute constant c0 of Theorem 5.21 in Λ_{s,q} → c0 = 54; reason: "The proof gives c0 = 54" (p. 44, PDF p. 47)
--   - encoding: N = 2^n, N^{1/3}, N^{−1/3}, √N → (2 : ℝ)^n with Real.rpow and Real.sqrt; reason: Lean convention; same values
-- source:
--   Bhateja, Esmaili, Mantri, Tight Query Lower Bounds for Quantum Sampling, with an Application to Certified Randomness, arXiv:2610.06721 (version of sha256 00a999f1…), Theorem 5.25, p. 45 (PDF p. 48)

import Mathlib
import Definitions.Def_TightQLB_Supplement_UnitaryAccess
open QAlgorithms MeasureTheory

set_option autoImplicit false

namespace TightQLB.Supplement

/-- **Theorem 5.25 (Haar lower bound for unitary access)**, p.45 (PDF p.48).

Bhateja, Esmaili, Mantri, *Tight Query Lower Bounds for Quantum Sampling, with an Application to
Certified Randomness*, arXiv:2610.06721 (version of sha256 00a999f1…).

"Let an algorithm make `q` queries to a Haar-random unitary, with inverse and controlled access.
Then `B(A) ≤ β_N + 2√2 Λ_{0,2q} + 72 Λ²_{0,2q} + (5q + 2)H_N/√N`. Consequently, there is an absolute
constant `c₃ > 0` such that, for every `0 < ε ≤ 1` and every `N` with
`(5N^{1/3} + 2)(ln N + 1) ≤ ε√N/2`, a score of `2 + ε` requires at least `c₃ ε^{2/3} N^{1/3}`
queries."

**Formalization Note.**
* An algorithm is `UnitaryExperiment n q W E` (Kretschmer's model in channel form: each of the `q`
  slots one query to `U`, `U†`, controlled `U` or controlled `U†`); `μ` is the Haar law on `U(N)`
  (`IsHaarUnitaryLaw`), and `B(A)` is `A.score μ`.
* `Λ_{0,2q}` is `Lam n 0 (2q)` (with `c₀ = 54`), `H_N` is `harmonicN n`, `N = 2^n`, `n ≥ 1`.
* "A score of `2 + ε` requires" is read as `B(A) ≥ 2 + ε`. The constant `c₃` is chosen before `n`,
  `ε`, the algorithm, its registers and `μ`. -/
theorem theorem_5_25 :
    (∀ {n q : ℕ}, 1 ≤ n → ∀ {W E : Type} [Fintype W] [DecidableEq W] [Fintype E] [DecidableEq E]
      (μ : Measure (Qubits n → Qubits n → ℂ)), IsHaarUnitaryLaw μ →
      ∀ A : UnitaryExperiment n q W E,
        A.score μ ≤ betaN n + 2 * Real.sqrt 2 * Lam n 0 (2 * q) + 72 * Lam n 0 (2 * q) ^ 2 +
          (5 * q + 2) * harmonicN n / Real.sqrt ((2 : ℝ) ^ n)) ∧
    ∃ c₃ : ℝ, 0 < c₃ ∧ ∀ n : ℕ, 1 ≤ n → ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      (5 * ((2 : ℝ) ^ n) ^ (1 / 3 : ℝ) + 2) * (Real.log ((2 : ℝ) ^ n) + 1) ≤
        ε * Real.sqrt ((2 : ℝ) ^ n) / 2 →
      ∀ (q : ℕ) {W E : Type} [Fintype W] [DecidableEq W] [Fintype E] [DecidableEq E]
        (μ : Measure (Qubits n → Qubits n → ℂ)), IsHaarUnitaryLaw μ →
        ∀ A : UnitaryExperiment n q W E, 2 + ε ≤ A.score μ →
          c₃ * ε ^ (2 / 3 : ℝ) * ((2 : ℝ) ^ n) ^ (1 / 3 : ℝ) ≤ q := by sorry

end TightQLB.Supplement
