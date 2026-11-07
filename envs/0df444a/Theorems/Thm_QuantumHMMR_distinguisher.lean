-- Prove2me | Theorems.Thm_QuantumHMMR_distinguisher
-- name    : QuantumHMMR.distinguisher
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:40:52.157206+00:00
-- url     : https://prove2.me/theorems/064c6c69-2423-40aa-9c54-725eb7020208
-- title:
--   Proof of Theorem 1.3, p.16 — the test of Lemma 4.4 separates the walk from Haar
-- statement:
--   Let $D'(n, h)$ be a family of copy tests with the guarantees of Lemma 4.4: $12h + 10$ copies, acceptance at least $5/8$ on unit vectors $\psi$ with $\dim S(\psi) \ge n - h$, and Haar acceptance at most $1/2 + 2^{-cn}$ for large $n$, whenever $19 \le h \le n - 2$. Set $h_n = 2T/m = 6\lceil\log^2 n\rceil$, prepare $12h_n + 10 = O(\log^2 n)$ copies of $U|0^n\rangle$ by parallel forward queries and apply $D'(n, h_n)$. Then:
--
--   1. the number of copies is $O(\log^2 n)$;
--   2. the Haar acceptance is at most $1/2 + 2^{-\Omega(n)}$;
--   3. for every admissible generating set $G$ and every integer $A \ge 1$, with $m = An^2$ and $T = 3m\lceil\log^2 n\rceil$, the acceptance under $U \sim \nu_n^{*T}$ is at least $5/8 - e^{-\Omega(\log^2 n)}$.
--
--   This is the pseudorandomness-breaking half of Theorem 1.3.
--
--   Differences from the source:
--   - generalization: the test of Lemma 4.4 → any family D′ with Lemma 4.4's copy count and acceptance guarantees; reason: the test of Lemma 4.4 is such a family; uniformity plays no role in the acceptance bounds
--   - generalization: the walk with m = A_t n² for the fixed G → every admissible G and every integer A ≥ 1; reason: the argument uses only m ≥ 2 and T/m = 3⌈log² n⌉
--   - reading: log² n, base not printed → (log_β n)² for an arbitrary base β > 1; reason: covers every reading of the base
--   - reading: O(log² n), 2^{−Ω(n)}, e^{−Ω(log² n)} → explicit constants C, c₂ > 0 and c₁ > 0 (c₁ may depend on G and A) with the bounds for n ≥ n₀; reason: the meaning of O and Ω
-- source:
--   Dujmovic–Haferkamp–Poremba, On the pseudorandomness of simple quantum processes, arXiv:2610.02100 (held version sha256 9920ec45…), proof of Theorem 1.3, p.16

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P45
import Definitions.Def_QuantumHMMR_IsCliffordGenSet
import Definitions.Def_QuantumHMMR_walkLaw
import Definitions.Def_QuantumHMMR_CopyTest
import Definitions.Def_QuantumHMMR_stabDim
import Definitions.Def_QuantumHMMR_logSq

open QAlgorithms QAlgorithms.Papers.Independent.Extend50.P45 MeasureTheory

namespace QuantumHMMR

attribute [local instance] QAlgorithms.Papers.Independent.Extend50.P45.qubitMatrixMeasurable

/-- **The distinguisher** (Dujmovic–Haferkamp–Poremba, *On the pseudorandomness of simple quantum processes*, arXiv:2610.02100 (held version, sha256 9920ec45…4f20), proof of Theorem 1.3, p.16). With `h = 2T/m = 6⌈log² n⌉`, prepare
`12h + 10 = O(log² n)` copies of `U|0ⁿ⟩` by parallel forward queries and apply the test of Lemma 4.4.
The walk acceptance is at least `5/8 - e^{-Ω(log² n)}`, while the Haar acceptance is at most
`1/2 + 2^{-Ω(n)}`.

Precisely: let `D'(n, h)` be any family of copy tests with the acceptance guarantees of Lemma 4.4
(acceptance `≥ 5/8` on states with `dim S(ψ) ≥ n - h`, and `≤ 1/2 + 2^{-cn}` on Haar-random states,
for `19 ≤ h ≤ n - 2`) using `12h + 10` copies. Then with `h_n = 6⌈log² n⌉`: the number of copies of
`D'(n, h_n)` is `O(log² n)`; its Haar acceptance is at most `1/2 + 2^{-c₂ n}` for large `n`; and for
every generating set `G` and every integer `A ≥ 1`, its acceptance on the walk `ν_n^{*T}` with
`m = A n²`, `T = 3m⌈log² n⌉` is at least `5/8 - e^{-c₁ log² n}` for large `n`.

**Formalization Note** `log² n = (log_β n)²` for an arbitrary base `β > 1`. "Apply Lemma 4.4" is
rendered by taking the guarantees of Lemma 4.4 as hypotheses on `D'` (any family with them; the
uniformity of Lemma 4.4 plays no role in the acceptance bounds). `Ω(·)` constants are explicit
`c₁, c₂ > 0`; `c₁` may depend on `G` and `A`. -/
theorem distinguisher (β : ℝ) (hβ : 1 < β) (D' : (p : ℕ × ℕ) → CopyTest p.1)
    (hK : ∀ n h : ℕ, (D' (n, h)).K = 12 * h + 10)
    (hacc : ∀ n h : ℕ, 19 ≤ h → h ≤ n - 2 → ∀ ψ : EuclideanSpace ℂ (Qubits n), IsState ψ →
      n - h ≤ stabDim ψ → (5 / 8 : ℝ) ≤ (D' (n, h)).accept ψ)
    (hhaar : ∃ c : ℝ, 0 < c ∧ ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ h : ℕ, 19 ≤ h → h ≤ n - 2 →
      ∫ U, (D' (n, h)).accept (act U (zeroKet n)) ∂haarLaw n ≤ 1 / 2 + (2 : ℝ) ^ (-(c * n))) :
    (∃ C : ℝ, ∃ n₀ : ℕ, ∀ n ≥ n₀,
      ((D' (n, 6 * ⌈logSq β n⌉₊)).K : ℝ) ≤ C * logSq β n) ∧
    (∃ c₂ : ℝ, 0 < c₂ ∧ ∃ n₀ : ℕ, ∀ n ≥ n₀,
      ∫ U, (D' (n, 6 * ⌈logSq β n⌉₊)).accept (act U (zeroKet n)) ∂haarLaw n ≤
        1 / 2 + (2 : ℝ) ^ (-(c₂ * n))) ∧
    ∀ G : Finset (Clifford.ProjectiveGroup 2), IsCliffordGenSet G → ∀ A : ℕ, 1 ≤ A →
      ∃ c₁ : ℝ, 0 < c₁ ∧ ∃ n₀ : ℕ, ∀ n ≥ n₀,
        (5 / 8 : ℝ) - Real.exp (-(c₁ * logSq β n)) ≤
          ∫ U, (D' (n, 6 * ⌈logSq β n⌉₊)).accept (act U (zeroKet n))
            ∂walkLaw G n (A * n ^ 2) (3 * (A * n ^ 2) * ⌈logSq β n⌉₊) := by sorry

end QuantumHMMR
