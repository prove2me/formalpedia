-- Prove2me | Theorems.Thm_RandModSubsetSum_theorem_7_1
-- name    : RandModSubsetSum.theorem_7_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T22:02:25.001941+00:00
-- url     : https://prove2.me/theorems/995f5c96-da45-43ef-9735-8d02b615edc8
-- title:
--   Theorem 7.1 — $\mathrm{Mod}_{\rm near}(n,Q)$ via bounded integer searches
-- statement:
--   Fix $B>\delta_0$. For $\delta_0n\le\log_2Q\le Bn$ and a fixed root $x$ nearly balanced in every stratum, let $a$ be uniform in $(\mathbb Z/Q\mathbb Z)^n$ and $t=a\cdot x\bmod Q$; the input is $(Q,a,t)$ and any binary solution of $a\cdot y\equiv t\pmod Q$ is acceptable. There is an algorithm (at most $(n+1)^{14}$ bounded calls to the integer search of Theorem 3.2) such that:
--
--   1. every run halts with FAIL or a binary solution, within time $(n+1)^{14}2^{0.261395n}+\mathrm{poly}_B(n)$ and space $2^{0.23728n}+\mathrm{poly}_B(n)$;
--   2. for sufficiently large $n$, every run uses at most $2^{0.261398n}$ bit operations and $2^{0.23729n}$ bits, and $\Pr(\text{FAIL})\le2^{-\Omega_B(n)}$ over the coefficients and the coins.
--
--   **Formalization Note** Machine `TwMSOCount.Main`; one program for all $B$; $\mathrm{poly}_B(n)=C(n+1)^K$ and $2^{-\Omega_B(n)}=2^{-cn}$ with constants chosen after $B$; strata use the paper's weights.
--
--   Differences from the source:
--   - reading: Fix B > δ₀ … Mod_near(n, Q) is solved by at most (n+1)^{14} bounded calls to the integer search → one program P, chosen before B, with the stated bounds; reason: the stronger of the two quantifier orders; the procedure is abstracted to a program with its stated properties
--   - encoding: poly_B(n), 2^{−Ω_B(n)}, sufficiently large n → C (n+1)^K, 2^{−cn}, n ≥ N with C, K, c, N chosen after B; reason: Lean convention
--   - encoding: input (Q, a, t), the strata of §6 → the word (Q, t, a₁, …, a_n) with canonical representatives; the paper's weights W_r/10²⁰; reason: machine words; §7 fixes the weights of §6
-- source:
--   Kim, Kim, Lee, Faster Provable Algorithm For Random Modular Subset Sum, STOC 2027 submission manuscript (sha256 c37a38c7…f89), Theorem 7.1, p. 53; Mod_near, p. 53

import Mathlib
import Definitions.Def_TwMSOCount_Main_Machine
import Definitions.Def_RandModSubsetSum_Strata
import Definitions.Def_RandModSubsetSum_Problem

open MeasureTheory TwMSOCount.Main
open scoped BigOperators ENNReal

namespace RandModSubsetSum

/-- **Theorem 7.1** (`Int_near(n, Q) ⇐ Mod_near(n, Q)`). Kim, Kim, Lee, *Faster Provable Algorithm For Random Modular Subset Sum*, STOC 2027 submission
manuscript (sha256 c37a38c7…f89), Theorem 7.1, p. 53, for the problem
`Mod_near(n, Q)` of p. 53.

Fix `B > δ₀` and `δ₀ n ≤ log Q ≤ B n`. The modular problem with a fixed hidden root nearly balanced
in every stratum (`x` fixed, `a` uniform in `(Z/QZ)ⁿ`, `t = a · x mod Q`, input `(Q, a, t)`, any
binary solution acceptable) is solved with failure `2^{−Ω_B(n)}`, time at most
`(n + 1)^{14} 2^{0.261395 n} + poly_B(n)` and space at most `2^{0.23728 n} + poly_B(n)`; for
sufficiently large `n`, at most `2^{0.261398 n}` bit operations and `2^{0.23729 n}` bits on every run.

**Formalization Note.** Machine `TwMSOCount.Main`. The algorithm (at most `(n+1)^{14}` bounded calls
to the integer search) is abstracted into one program `P`, chosen before `B` (the stronger reading
of "Fix `B` … is solved by"). `poly_B(n) = C (n + 1)^K` and `2^{−Ω_B(n)}`, "sufficiently large `n`"
are constants chosen after `B`. Strata use the paper's weights. The input word is
`(Q, t, a_1, …, a_n)` with canonical representatives; FAIL is the empty word. -/
theorem theorem_7_1 :
    ∃ P : Program, ∀ B : ℝ, delta0 < B →
      ∃ c : ℝ, 0 < c ∧ ∃ C : ℝ, ∃ K N : ℕ,
        (∀ n : ℕ, 1 ≤ n → ∀ Q : ℕ, InRange B n Q → ∀ x : Fin n → Fin 2, NearBalanced paperWeight x →
          ∀ (a : Fin n → Fin Q) (τ : ℕ → Bool),
            ∃ s, runStats P τ (Config.init (modInput a (modTarget a x))) = some s ∧
              (s.time : ℝ) ≤ ((n : ℝ) + 1) ^ 14 * (2 : ℝ) ^ ((261395 / 10 ^ 6 : ℝ) * n) +
                C * ((n : ℝ) + 1) ^ K ∧
              (s.space : ℝ) ≤ (2 : ℝ) ^ ((23728 / 10 ^ 5 : ℝ) * n) + C * ((n : ℝ) + 1) ^ K ∧
              FailOrModSolution a (modTarget a x) s.final.output) ∧
        (∀ n : ℕ, N ≤ n → ∀ Q : ℕ, InRange B n Q → ∀ x : Fin n → Fin 2, NearBalanced paperWeight x →
          (∀ (a : Fin n → Fin Q) (τ : ℕ → Bool),
            ∃ s, runStats P τ (Config.init (modInput a (modTarget a x))) = some s ∧
              (s.time : ℝ) ≤ (2 : ℝ) ^ ((261398 / 10 ^ 6 : ℝ) * n) ∧
              (s.space : ℝ) ≤ (2 : ℝ) ^ ((23729 / 10 ^ 5 : ℝ) * n)) ∧
          (∑ a : Fin n → Fin Q,
              coinTape {τ | callOutput P (Config.init (modInput a (modTarget a x))) τ = some []}) ≤
            ENNReal.ofReal ((2 : ℝ) ^ (-c * n)) * (Q : ℝ≥0∞) ^ n) := by sorry

end RandModSubsetSum
