-- Prove2me | Theorems.Thm_SelectiveDPT_proposition_2_7
-- name    : SelectiveDPT.proposition_2_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T12:51:58.762121+00:00
-- url     : https://prove2.me/theorems/fa019b0e-97fb-45f9-aa2e-2866a6eccc5f
-- title:
--   Proposition 2.7 [LMR+11] — $Q_{1/10}(f) = O(\mathrm{ADV}^\pm_{1/10}(f))$
-- statement:
--   There is a constant $C > 0$ such that for every alphabet size $d \ge 1$, every $n \ge 1$, every set $Y$, every domain $D \subseteq X^n$ and every function $f : D \to Y$,
--   $$Q_{1/10}(f) \le C \cdot \mathrm{ADV}^\pm_{1/10}(f) .$$
--
--   This is the optimality of the negative-weights adversary method for functions, due to Lee, Mittal, Reichardt, Špalek and Szegedy; the paper cites it and does not prove it. Remark 2.8 explains the passage from their $Q_{1/3}$ and zero-error $\mathrm{ADV}^\pm$ to error $1/10$ on both sides.
--
--   Differences from the source:
--   - reading: Q_{1/10}(f) = O(ADV±_{1/10}(f)) → one constant C > 0 chosen before d, n, Y, D and f; reason: the O(·) is uniform over all functions
--   - reading: ADV±_{1/10}(f) of Definition 2.6 → ADV± with the general τ±(ε) for every Y; reason: Definition 2.6 refers to Proposition 2.5, whose general τ± holds for every Y; for Boolean Y the tightened τ± changes ADV± at ε = 1/10 by the factor (1 − 0.6)/(1 − 0.7) = 4/3, absorbed in C
--   - encoding: D ⊆ X^n (n arbitrary) → 0 < n; reason: with n = 0 the query register Fin 0 × Z_d of QueryAlg is empty, so no algorithm exists and Q = ⊤ in Lean, while the paper's Q is 0 there; the hypothesis only excludes this degenerate encoding
--   - encoding: inputs x ∈ X^n with |X| = d, a T-query algorithm measuring its work register and post-processing the result → X = ZMod d, inputs Fin n → ZMod d with a Finset domain D, QAlgorithms.QueryAlg with workspace Fin b for any b, a full computational-basis measurement followed by an output map, query complexity in ℕ∞ (⊤ if no algorithm exists) compared in [0, ∞]; reason: relabelling X as Z_d is the paper's own convention (p.9); only the workspace dimension matters; measuring a designated output register is a special output map
-- source:
--   Beame–Kornerup–Whitmeyer, Strong Selective and List-Decoding Direct Product Theorems for Quantum Query Complexity, arXiv:2609.26678, Proposition 2.7 and Remark 2.8, p.13 (restated p.25)

import Mathlib
import Definitions.Def_SelectiveDPT_Qfun
import Definitions.Def_SelectiveDPT_advPm

open scoped ENNReal

universe u

namespace SelectiveDPT

/-- Proposition 2.7 of arXiv:2609.26678 (Beame–Kornerup–Whitmeyer), p.13 (restated p.25), cited
from Lee–Mittal–Reichardt–Špalek–Szegedy [LMR+11]; the paper does not prove it: for any function
`f : D → Y` where `D ⊆ X^n`, `Q_{1/10}(f) = O(ADV±_{1/10}(f))`. Remark 2.8 (p.13) explains the
passage from `[LMR+11]`'s `Q_{1/3}` and zero-error `ADV±` to error `1/10` on both sides.

**Formalization Note.** `O(·)` is one constant `C > 0` chosen before `d`, `n`, `Y`, `D` and `f`.
`n ≥ 1`: with `n = 0` the query register `Fin 0 × Z_d` of `QAlgorithms.QueryAlg` is empty, no
algorithm exists and `Q = ⊤`, while the paper's inputs have at least one position. -/
theorem proposition_2_7 :
    ∃ C : ℝ, 0 < C ∧ ∀ (d n : ℕ) [NeZero d], 0 < n → ∀ (Y : Type u)
      (D : Finset (Fin n → ZMod d)) (f : (Fin n → ZMod d) → Y),
      (Qfun D f (1 / 10) : ℝ≥0∞) ≤ ENNReal.ofReal C * advPm D f (1 / 10) := by sorry

end SelectiveDPT
