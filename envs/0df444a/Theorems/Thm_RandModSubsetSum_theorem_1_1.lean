-- Prove2me | Theorems.Thm_RandModSubsetSum_theorem_1_1
-- name    : RandModSubsetSum.theorem_1_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T22:02:50.075195+00:00
-- url     : https://prove2.me/theorems/b8e7dac9-ca2b-4bee-8ec1-6da64e4ad2c1
-- title:
--   Theorem 1.1 — balanced random modular subset sum in $2^{0.2614n}$ bit operations and $2^{0.2373n}$ bits with failure $\le2^{-c_Bn}$
-- statement:
--   Put $\delta_0=0.999996$. Fix $B>\delta_0$, and put $\beta=\max\{B,2\}$ and $c_B=\min\{10^{-24},(100\beta)^{-1}\}$. There is a randomized algorithm with the following guarantee for every even $n\ge\max\{10^{26},10^6\beta\}$, every integer $Q$ with $2^{\delta_0n}\le Q\le2^{Bn}$, and every fixed $x\in\{0,1\}^n$ with $\sum_ix_i=n/2$. Sample $a$ uniformly in $(\mathbb Z/Q\mathbb Z)^n$, independently of $x$, and set $t=a\cdot x\pmod Q$. Given $(a,t,Q)$, the algorithm returns a binary solution $y$ with $a\cdot y\equiv t\pmod Q$ or FAIL, with
--
--   $$\Pr(\mathrm{FAIL})\le2^{-c_Bn},$$
--
--   the probability over the coefficients and the algorithm's randomness. Every run uses at most $2^{0.2614n}$ bit operations and $2^{0.2373n}$ bits of space, including input and auxiliary storage.
--
--   Its time exponent $0.2614$ is below those of the earlier classical algorithms compared in Table 1 of the paper: $0.291+3\varepsilon$ for BCJ without heuristic assumptions, and $0.283$ for BBSS with a heuristic assumption.
--
--   **Formalization Note** The machine is the published randomized log-cost RAM `TwMSOCount.Main`: an arithmetic step on operands of $\ell_1,\ell_2$ bits costs $(\ell_1+\ell_2+1)^2$ bit operations; space counts the address and content bits of every cell ever written, the input included; coins are a fair tape. The program depends on $B$ only.
--
--   Differences from the source:
--   - encoding: bit operations and bits of space, including input and auxiliary storage → RunStats.time and RunStats.space of TwMSOCount.Main; reason: the paper's implementation model (App. C.2) differs by polynomial factors, absorbed by the margins 2^{2·10⁻⁶n} and 2^{10⁻⁵n} at n ≥ 10²⁶
--   - encoding: given (a, t, Q); output y or FAIL → the word (Q, t, a₁, …, a_n) with canonical representatives; output y₁, …, y_n, FAIL the empty word; reason: machine words
--   - encoding: Pr(FAIL) over uniform a and the coins → Σ_a coinTape{FAIL} ≤ 2^{−c_B n} Qⁿ; reason: division-free form of the average over the Qⁿ coefficient vectors
--   - encoding: δ₀ = 0.999996, 0.2614, 0.2373, 2^{(·)} → exact rationals, real powers; reason: Lean convention
--   - encoding: x ∈ {0,1}ⁿ with Σ x_i = n/2 → x : Fin n → Fin 2 with #{i : x_i = 1} = n/2; reason: Lean convention
--   - reading: every run → every coefficient vector a ∈ (Z/QZ)ⁿ, the target t = a·x mod Q, and every coin tape; reason: the support of the input distribution
-- source:
--   Kim, Kim, Lee, Faster Provable Algorithm For Random Modular Subset Sum, STOC 2027 submission manuscript (sha256 c37a38c7…f89), Theorem 1.1, p. 3

import Mathlib
import Definitions.Def_TwMSOCount_Main_Machine
import Definitions.Def_RandModSubsetSum_Problem

open MeasureTheory TwMSOCount.Main
open scoped BigOperators ENNReal

namespace RandModSubsetSum

/-- **Theorem 1.1** (random modular subset sum). Kim, Kim, Lee, *Faster Provable Algorithm For Random Modular Subset Sum*, STOC 2027 submission
manuscript (sha256 c37a38c7…f89), Theorem 1.1, p. 3.

Put `δ₀ = 0.999996`. Fix `B > δ₀`, and put `β = max{B, 2}`, `c_B = min{10⁻²⁴, (100β)⁻¹}`. There is
a randomized algorithm with the following guarantee for every even `n ≥ max{10²⁶, 10⁶ β}`, all
integers `2^{δ₀ n} ≤ Q ≤ 2^{B n}`, and every fixed `x ∈ {0, 1}ⁿ` with `Σ_i x_i = n/2`. Sample `a`
uniformly in `(Z/QZ)ⁿ`, independently of `x`, and set `t = a · x (mod Q)`. Given `(a, t, Q)`, the
algorithm returns a binary solution `y` with `a · y ≡ t (mod Q)` or FAIL, with
`Pr(FAIL) ≤ 2^{−c_B n}`. The probability is over the coefficients and the algorithm's randomness.
Every run uses at most `2^{0.2614 n}` bit operations and `2^{0.2373 n}` bits of space.

**Formalization Note.** The machine is the published randomized log-cost RAM `TwMSOCount.Main`:
bit time (each arithmetic step on operands of `ℓ₁, ℓ₂` bits costs `(ℓ₁ + ℓ₂ + 1)²`), bit space
(address and content bits of every cell ever written, input cells included), and a fair coin tape.
The program is chosen after `B` and before `n, Q, x, a` and the coins. The input word is
`(Q, t, a_1, …, a_n)` with canonical representatives in `{0, …, Q − 1}`; FAIL is the empty word and a
solution `y` is the word `y_1, …, y_n`. Costs and validity hold for every `a` and every coin tape.
`Pr(FAIL) = Q^{−n} Σ_a coinTape{FAIL}`, stated without division. The decimals are exact rationals
and `2^{(·)}` is the real power. -/
theorem theorem_1_1 :
    ∀ B : ℝ, delta0 < B →
    ∃ P : Program,
    ∀ n : ℕ, Even n → max ((10 : ℝ) ^ 26) ((10 : ℝ) ^ 6 * beta B) ≤ n →
    ∀ Q : ℕ, InRange B n Q →
    ∀ x : Fin n → Fin 2, IsBalanced x →
      (∀ (a : Fin n → Fin Q) (τ : ℕ → Bool),
        ∃ s, runStats P τ (Config.init (modInput a (modTarget a x))) = some s ∧
          (s.time : ℝ) ≤ (2 : ℝ) ^ ((2614 / 10 ^ 4 : ℝ) * n) ∧
          (s.space : ℝ) ≤ (2 : ℝ) ^ ((2373 / 10 ^ 4 : ℝ) * n) ∧
          FailOrModSolution a (modTarget a x) s.final.output) ∧
      (∑ a : Fin n → Fin Q,
          coinTape {τ | callOutput P (Config.init (modInput a (modTarget a x))) τ = some []}) ≤
        ENNReal.ofReal ((2 : ℝ) ^ (-(cB B) * n)) * (Q : ℝ≥0∞) ^ n := by sorry

end RandModSubsetSum
