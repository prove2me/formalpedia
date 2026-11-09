-- Prove2me | Theorems.Thm_SelectiveDPT_theorem_3_7
-- name    : SelectiveDPT.theorem_3_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T12:54:40.566449+00:00
-- url     : https://prove2.me/theorems/92dd5413-9888-46f5-a668-737f8818717e
-- title:
--   Theorem 3.7 (corrected: $D$ nonempty) — $Q_{1/10}(f) \le C\cdot\mathrm{MADV}^{\mathcal D}_{1/10,\lambda,\eta}(f)$
-- statement:
--   There is a constant $C > 0$ such that for every alphabet size $d \ge 1$, every $n \ge 1$, every set $Y$, every **nonempty** domain $D \subseteq X^n$ and every function $f : D \to Y$ there is a distribution $\mathcal D$ on $D$ with
--   $$Q_{1/10}(f) \le C \cdot \mathrm{MADV}^{\mathcal D}_{\varepsilon,\lambda,\eta}(f)$$
--   for $\varepsilon = 1/10$, $\lambda = 3 - (4/(1-\varepsilon))^{1/3} \approx 1.356$ and $\eta = ((1-\varepsilon)/4)^{1/3} \approx 0.608$.
--
--   So the relational multiplicative adversary method characterizes the bounded-error quantum query complexity of every function up to a constant factor.
--
--   Differences from the source:
--   - correction: for any function f : D → Y where D ⊆ X^n there is a distribution D on D → D nonempty; reason: for D = ∅ (any n ≥ 1, any d, any f) no distribution on D exists, while Q_{1/10}(f) = 0
--   - reading: there is a constant C > 0 → C chosen before d, n, Y, D and f; λ and η as the exact expressions at ε = 1/10; reason: the statement fixes C before f; the decimals 1.356 and 0.608 are approximations
--   - encoding: D ⊆ X^n (n arbitrary) → 0 < n; reason: with n = 0 the query register Fin 0 × Z_d of QueryAlg is empty, so no algorithm exists and Q = ⊤ in Lean, while the paper's Q is 0 there; the hypothesis only excludes this degenerate encoding
--   - encoding: inputs x ∈ X^n with |X| = d, a T-query algorithm measuring its work register and post-processing the result → X = ZMod d, inputs Fin n → ZMod d with a Finset domain D, QAlgorithms.QueryAlg with workspace Fin b for any b, a full computational-basis measurement followed by an output map, query complexity in ℕ∞ (⊤ if no algorithm exists) compared in [0, ∞]; reason: relabelling X as Z_d is the paper's own convention (p.9); only the workspace dimension matters; measuring a designated output register is a special output map
-- source:
--   Beame–Kornerup–Whitmeyer, Strong Selective and List-Decoding Direct Product Theorems for Quantum Query Complexity, arXiv:2609.26678, Theorem 3.7, p.25

import Mathlib
import Definitions.Def_SelectiveDPT_Qfun
import Definitions.Def_SelectiveDPT_madv

open scoped ENNReal

universe u

namespace SelectiveDPT

/-- Theorem 3.7 of arXiv:2609.26678 (Beame–Kornerup–Whitmeyer), p.25: there is a constant `C > 0`
such that for any function `f : D → Y` where `D ⊆ X^n` there is a distribution `D` on `D` such
that `Q_{1/10}(f)` is at most `C · MADV^D_{ε,λ,η}(f)` for `ε = 1/10`,
`λ = 3 − (4/(1−ε))^{1/3} ≈ 1.356` and `η = ((1−ε)/4)^{1/3} ≈ 0.608`.

**Formalization Note.** `C` is chosen before `d`, `n`, `Y`, `D`, `f`; `λ` and `η` are the exact
expressions at `ε = 1/10`. `n ≥ 1` as in Proposition 2.7 (empty query register). **Correction:**
`D` is nonempty — for `D = ∅` no distribution on `D` exists while `Q_{1/10}(f) = 0`. -/
theorem theorem_3_7 :
    ∃ C : ℝ, 0 < C ∧ ∀ (d n : ℕ) [NeZero d], 0 < n → ∀ (Y : Type u)
      (D : Finset (Fin n → ZMod d)) (f : (Fin n → ZMod d) → Y), D.Nonempty →
      ∃ μ : (Fin n → ZMod d) → ℝ, IsDistOn μ D ∧
        (Qfun D f (1 / 10) : ℝ≥0∞) ≤ ENNReal.ofReal C *
          madv μ D (fun x y => f x = y) (1 / 10) (3 - (4 / (1 - 1 / 10)) ^ ((1 : ℝ) / 3))
            (((1 - 1 / 10) / 4) ^ ((1 : ℝ) / 3)) := by sorry

end SelectiveDPT
