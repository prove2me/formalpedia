-- Prove2me | Theorems.Thm_RandModSubsetSum_theorem_7_2
-- name    : RandModSubsetSum.theorem_7_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T22:02:31.007198+00:00
-- url     : https://prove2.me/theorems/9798c5f9-af7c-44d8-9967-db570d07833c
-- title:
--   Theorem 7.2 — $\mathrm{Mod}_{\rm bal}(n,Q)$ via a uniform coordinate permutation
-- statement:
--   Fix $B>\delta_0$. For even $n$, $\delta_0n\le\log_2Q\le Bn$, and a fixed root $x$ with exactly $n/2$ ones, let $a$ be uniform in $(\mathbb Z/Q\mathbb Z)^n$ and $t=a\cdot x\bmod Q$; the input is $(Q,a,t)$. Reducing to Theorem 7.1 by a uniform coordinate permutation gives a solver that always halts with FAIL or a binary solution of $a\cdot y\equiv t\pmod Q$, and, for sufficiently large $n$, has failure probability $2^{-\Omega_B(n)}$ over the coefficients and the coins and uses at most $2^{0.261398n}$ bit operations and $2^{0.23729n}$ bits on every run.
--
--   Together with Appendix C, which makes the constants explicit, this is the algorithm of Theorem 1.1.
--
--   **Formalization Note** Machine `TwMSOCount.Main`; one program for all $B$; $2^{-\Omega_B(n)}=2^{-cn}$ and the threshold $N$ are chosen after $B$.
--
--   Differences from the source:
--   - reading: Mod_bal(n, Q) reduces to Mod_near(n, Q) by a uniform coordinate permutation; the resulting solver … → one program P, chosen before B, with the stated properties; reason: the procedure is abstracted to a program; the stronger quantifier order
--   - reading: aggregate limits 2^{0.261398n} and 2^{0.23729n} → these limits for n ≥ N(B); reason: read with the same threshold as Theorem 7.1 ("For sufficiently large n", p. 53), whose bounds the solver inherits
--   - encoding: 2^{−Ω_B(n)}; input (Q, a, t) → ∃ c > 0, N after B, Σ_a coinTape(FAIL) ≤ 2^{−cn}Qⁿ; the word (Q, t, a₁, …, a_n); reason: Lean convention
-- source:
--   Kim, Kim, Lee, Faster Provable Algorithm For Random Modular Subset Sum, STOC 2027 submission manuscript (sha256 c37a38c7…f89), Theorem 7.2, p. 54; Mod_bal, p. 53

import Mathlib
import Definitions.Def_TwMSOCount_Main_Machine
import Definitions.Def_RandModSubsetSum_Problem

open MeasureTheory TwMSOCount.Main
open scoped BigOperators ENNReal

namespace RandModSubsetSum

/-- **Theorem 7.2** (`Mod_near(n, Q) ⇐ Mod_bal(n, Q)`). Kim, Kim, Lee, *Faster Provable Algorithm For Random Modular Subset Sum*, STOC 2027 submission
manuscript (sha256 c37a38c7…f89), Theorem 7.2, p. 54, for the problem
`Mod_bal(n, Q)` of p. 53.

For even `n` in the modulus range `δ₀ n ≤ log₂ Q ≤ B n`, the modular problem with a fixed hidden
root having exactly `n/2` ones (`x` fixed, `a` uniform in `(Z/QZ)ⁿ`, `t = a · x mod Q`, input
`(Q, a, t)`, any binary solution acceptable) is solved, by a uniform coordinate permutation and the
solver of Theorem 7.1, with failure `2^{−Ω_B(n)}` and aggregate limits `2^{0.261398 n}` bit
operations and `2^{0.23729 n}` bits.

**Formalization Note.** Machine `TwMSOCount.Main`; the solver is one program `P` chosen before
`B`. `2^{−Ω_B(n)}` is `∃ c > 0, ∃ N` after `B`; the aggregate limits are read for `n ≥ N`, as in
Theorem 7.1 ("for sufficiently large `n`", p. 53). Halting with FAIL or a valid solution is claimed
for every even `n ≥ 1` in the range. -/
theorem theorem_7_2 :
    ∃ P : Program, ∀ B : ℝ, delta0 < B →
      ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ,
        (∀ n : ℕ, 1 ≤ n → Even n → ∀ Q : ℕ, InRange B n Q → ∀ x : Fin n → Fin 2, IsBalanced x →
          ∀ (a : Fin n → Fin Q) (τ : ℕ → Bool),
            ∃ s, runStats P τ (Config.init (modInput a (modTarget a x))) = some s ∧
              FailOrModSolution a (modTarget a x) s.final.output) ∧
        (∀ n : ℕ, N ≤ n → Even n → ∀ Q : ℕ, InRange B n Q → ∀ x : Fin n → Fin 2, IsBalanced x →
          (∀ (a : Fin n → Fin Q) (τ : ℕ → Bool),
            ∃ s, runStats P τ (Config.init (modInput a (modTarget a x))) = some s ∧
              (s.time : ℝ) ≤ (2 : ℝ) ^ ((261398 / 10 ^ 6 : ℝ) * n) ∧
              (s.space : ℝ) ≤ (2 : ℝ) ^ ((23729 / 10 ^ 5 : ℝ) * n)) ∧
          (∑ a : Fin n → Fin Q,
              coinTape {τ | callOutput P (Config.init (modInput a (modTarget a x))) τ = some []}) ≤
            ENNReal.ofReal ((2 : ℝ) ^ (-c * n)) * (Q : ℝ≥0∞) ^ n) := by sorry

end RandModSubsetSum
