-- Prove2me | Theorems.Thm_SelectiveDPT_Supplement_theorem_3_8
-- name    : SelectiveDPT.Supplement.theorem_3_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T00:33:54.1882+00:00
-- url     : https://prove2.me/theorems/7bc11a07-2470-40b5-aed2-26488421a944
-- title:
--   Theorem 3.8 (corrected: $D$ nonempty) — $Q_{1/10}(f) \le C\cdot\mathrm{MADV}^{\mathcal D}_{1/10,19/10,1/2}(f)$ for Boolean $f$
-- statement:
--   There is a constant $C > 0$ such that for every alphabet size $d \ge 1$, every $n \ge 1$, every **nonempty** domain $D \subseteq X^n$ and every Boolean function $f : D \to \{0,1\}$ there is a distribution $\mathcal D$ on $D$ with
--   $$Q_{1/10}(f) \le C \cdot \mathrm{MADV}^{\mathcal D}_{\varepsilon,\lambda,\eta}(f), \qquad \varepsilon = 1/10,\ \lambda = 19/10,\ \eta = 1/2 .$$
--
--   So for Boolean functions the relational multiplicative adversary method with $\eta = 1/2$ characterizes bounded-error quantum query complexity up to a constant factor.
--
--   Differences from the source:
--   - correction: for any function f : D → {0,1} where D ⊆ X^n there is a distribution D on D → D nonempty; reason: for D = ∅ (any n ≥ 1, any d, any f) no distribution on D exists, while Q_{1/10}(f) = 0; the base mission's correction of Theorem 3.7
--   - reading: there is a constant C > 0 → C chosen before d, n, D and f; reason: the statement fixes C before f
--   - encoding: D ⊆ X^n (n arbitrary) → 0 < n; reason: with n = 0 the query register Fin 0 × Z_d of QueryAlg is empty, so no algorithm exists and Q = ⊤ in Lean, while the paper's Q is 0 there; the hypothesis only excludes this degenerate encoding (as in the base Theorem 3.7)
--   - encoding: f : D → {0,1} → f : (Fin n → ZMod d) → Bool, read only on D; reason: {0,1} is Bool; values outside D are never read
--   - encoding: inputs x ∈ X^n with |X| = d, a T-query algorithm measuring its work register and post-processing the result → X = ZMod d, inputs Fin n → ZMod d with a Finset domain D, QAlgorithms.QueryAlg with workspace Fin b for any b, a full computational-basis measurement followed by an output map, query complexity in ℕ∞ (⊤ if no algorithm exists) compared in [0, ∞]; reason: relabelling X as Z_d is the paper's own convention (p.9); only the workspace dimension matters; measuring a designated output register is a special output map
-- source:
--   Beame–Kornerup–Whitmeyer, Strong Selective and List-Decoding Direct Product Theorems for Quantum Query Complexity, arXiv:2609.26678, Theorem 3.8, p.25

import Mathlib
import Definitions.Def_SelectiveDPT_Qfun
import Definitions.Def_SelectiveDPT_madv

open scoped ENNReal

namespace SelectiveDPT.Supplement

/-- Theorem 3.8 of arXiv:2609.26678 (Beame–Kornerup–Whitmeyer), p.25: there is a constant `C > 0`
such that for any function `f : D → {0,1}` where `D ⊆ X^n` there is a distribution `D` on `D` such
that `Q_{1/10}(f)` is at most `C · MADV^D_{ε,λ,η}(f)` for `ε = 1/10`, `λ = 19/10` and `η = 1/2`.

**Formalization Note.** As the base mission's Theorem 3.7: `C` is chosen before `d`, `n`, `D`,
`f`; `n ≥ 1` (with `n = 0` the query register is empty and `Q = ⊤` in Lean); **correction:** `D`
is nonempty (for `D = ∅` no distribution on `D` exists while `Q_{1/10}(f) = 0`). `{0,1}` is
`Bool`. -/
theorem theorem_3_8 :
    ∃ C : ℝ, 0 < C ∧ ∀ (d n : ℕ) [NeZero d], 0 < n → ∀ (D : Finset (Fin n → ZMod d))
      (f : (Fin n → ZMod d) → Bool), D.Nonempty →
      ∃ μ : (Fin n → ZMod d) → ℝ, IsDistOn μ D ∧
        (Qfun D f (1 / 10) : ℝ≥0∞) ≤ ENNReal.ofReal C *
          madv μ D (fun x y => f x = y) (1 / 10) (19 / 10) (1 / 2) := by sorry

end SelectiveDPT.Supplement
