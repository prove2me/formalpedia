-- Prove2me | Theorems.Thm_SelectiveDPT_theorem_4_9
-- name    : SelectiveDPT.theorem_4_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T12:53:22.939521+00:00
-- url     : https://prove2.me/theorems/3acd4f8d-2712-4f72-bb18-73a68cc8d259
-- title:
--   Theorem 4.9 — strong selective direct product theorem at $\varepsilon = 1/10$
-- statement:
--   Fix $\varepsilon = 1/10$. There are constants $\alpha, \gamma > 0$ and an integer $k_0 \ge 1$ such that for every alphabet size $d \ge 1$, every $n$, every set $Y$, every domain $D \subseteq X^n$, every function $f : D \to Y$ and all integers $k, m$ with $k_0 \le k \le m$,
--   $$Q_{1-(1-\varepsilon)^{\gamma k}}\big(f^{(k,m)}\big) \;\ge\; \alpha k \cdot Q_\varepsilon(f).$$
--
--   Both sides are worst-case query complexities. This is the paper's precise version of Theorem 1.9 at the error $1/10$.
--
--   Differences from the source:
--   - encoding: m-copy inputs in (X^n)^m, outputs ((i_1, y_1), …, (i_k, y_k)) with i_1 ≠ ⋯ ≠ i_k → inputs on Fin m × Fin n (copy, position), outputs Fin k → Fin m × Y with injective copy indices; reason: footnote 5 (p.9) indexes queries by (copy, position); an ordered injective tuple is a k-set of copies with labels (p.10)
--   - encoding: inputs x ∈ X^n with |X| = d, a T-query algorithm measuring its work register and post-processing the result → X = ZMod d, inputs Fin n → ZMod d with a Finset domain D, QAlgorithms.QueryAlg with workspace Fin b for any b, a full computational-basis measurement followed by an output map, query complexity in ℕ∞ (⊤ if no algorithm exists) compared in [0, ∞]; reason: relabelling X as Z_d is the paper's own convention (p.9); only the workspace dimension matters; measuring a designated output register is a special output map
-- source:
--   Beame–Kornerup–Whitmeyer, Strong Selective and List-Decoding Direct Product Theorems for Quantum Query Complexity, arXiv:2609.26678, Theorem 4.9 and its proof, p.37

import Mathlib
import Definitions.Def_SelectiveDPT_Qfun
import Definitions.Def_SelectiveDPT_prodDomain
import Definitions.Def_SelectiveDPT_selRel

open scoped ENNReal

universe u

namespace SelectiveDPT

/-- Theorem 4.9 of arXiv:2609.26678 (Beame–Kornerup–Whitmeyer), p.37: fix `ε = 1/10`. There are
constants `α, γ > 0` and an integer `k₀ ≥ 1` such that for `f : D → Y` where `D ⊆ X^n`, and for
all integers `k` with `k₀ ≤ k ≤ m`, `Q_{1−(1−ε)^{γk}}(f^(k,m)) ≥ αk · Q_ε(f)`.

**Formalization Note.** `α`, `γ`, `k₀` are chosen before `d`, `n`, `Y`, `D`, `f`, `k`, `m`. Both
sides are worst-case query complexities; `f^(k,m)` is the selective direct product of the graph of
`f` on `D^m`, with inputs indexed by `Fin m × Fin n`. The exponent `γk` is real. -/
theorem theorem_4_9 :
    ∃ α γ : ℝ, 0 < α ∧ 0 < γ ∧ ∃ k₀ : ℕ, 1 ≤ k₀ ∧
      ∀ (d n : ℕ) [NeZero d] (Y : Type u) (D : Finset (Fin n → ZMod d))
        (f : (Fin n → ZMod d) → Y) (k m : ℕ), k₀ ≤ k → k ≤ m →
        ENNReal.ofReal (α * k) * (Qfun D f (1 / 10) : ℝ≥0∞) ≤
          (Qrel (prodDomain D m) (selRel k m (fun x y => f x = y))
            (1 - (1 - 1 / 10 : ℝ) ^ (γ * k)) : ℝ≥0∞) := by sorry

end SelectiveDPT
