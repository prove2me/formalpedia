-- Prove2me | Theorems.Thm_SelectiveDPT_theorem_1_9
-- name    : SelectiveDPT.theorem_1_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T12:52:11.947582+00:00
-- url     : https://prove2.me/theorems/b6497964-69dd-4c50-a223-a60546de2652
-- title:
--   Theorem 1.9 — every function satisfies a quantum strong selective direct product theorem
-- statement:
--   There are constants $\gamma > 0$ and $k_0 \ge 1$ such that for every $\varepsilon \in (0, 1/10]$ there is $\alpha > 0$ with the following property. For every alphabet size $d \ge 1$, every $n$, every set $Y$, every domain $D \subseteq X^n$, every function $f : D \to Y$ and all integers $k, m$ with $k_0 \le k \le m$,
--   $$Q_{1-(1-\varepsilon)^{\gamma k}}\big(f^{(k,m)}\big) \;\ge\; \alpha\, k\, Q_\varepsilon(f).$$
--
--   Here $f^{(k,m)}$ is the selective direct product of $f$: given $m$ inputs in $D$, the algorithm must output $k$ pairs $(i_j, y_j)$ with pairwise distinct copy indices of its choice and $y_j = f(x_{i_j})$ for all $j$. The left side is the worst-case number of queries needed to succeed with probability at least $(1-\varepsilon)^{\gamma k}$ on every input of $D^m$; the right side involves the worst-case query complexity of $f$ at error $\varepsilon$. So an algorithm making fewer than $\alpha k Q_\varepsilon(f)$ queries answers its own choice of $k$ copies correctly only with probability exponentially small in $k$.
--
--   **Formalization Note** $\gamma$ and $k_0$ do not depend on $\varepsilon$; $\alpha$ does.
--
--   Differences from the source:
--   - generalization: for all sufficiently small constant ε > 0 (some threshold ε₀) → every ε ∈ (0, 1/10]; reason: fixing the threshold ε₀ = 1/10 is stronger than ∃ ε₀ and specializes to the source's claim with ε₀ = 1/10; Theorem 4.9 is the case ε = 1/10
--   - reading: Q_{1−(1−ε)^{γk}}(f^(k,m)) is Ω(k·Q_ε(f)) → ∃ α > 0 chosen after ε and before d, n, Y, D, f, k, m; reason: ε is a fixed constant, so the constant of Ω may depend on it but on nothing else
--   - generalization: k₀ ≤ k < m → k₀ ≤ k ≤ m; reason: the Lean statement also covers k = m and specializes to k < m; Theorem 4.9 has k ≤ m
--   - encoding: m-copy inputs in (X^n)^m, outputs ((i_1, y_1), …, (i_k, y_k)) with i_1 ≠ ⋯ ≠ i_k → inputs on Fin m × Fin n (copy, position), outputs Fin k → Fin m × Y with injective copy indices; reason: footnote 5 (p.9) indexes queries by (copy, position); an ordered injective tuple is a k-set of copies with labels (p.10)
--   - encoding: inputs x ∈ X^n with |X| = d, a T-query algorithm measuring its work register and post-processing the result → X = ZMod d, inputs Fin n → ZMod d with a Finset domain D, QAlgorithms.QueryAlg with workspace Fin b for any b, a full computational-basis measurement followed by an output map, query complexity in ℕ∞ (⊤ if no algorithm exists) compared in [0, ∞]; reason: relabelling X as Z_d is the paper's own convention (p.9); only the workspace dimension matters; measuring a designated output register is a special output map
-- source:
--   Beame–Kornerup–Whitmeyer, Strong Selective and List-Decoding Direct Product Theorems for Quantum Query Complexity, arXiv:2609.26678, Theorem 1.9, p.5

import Mathlib
import Definitions.Def_SelectiveDPT_Qfun
import Definitions.Def_SelectiveDPT_prodDomain
import Definitions.Def_SelectiveDPT_selRel

open scoped ENNReal

universe u

namespace SelectiveDPT

/-- Theorem 1.9 of Beame–Kornerup–Whitmeyer, *Strong Selective and List-Decoding Direct Product
Theorems for Quantum Query Complexity*, arXiv:2609.26678, p.5: every function satisfies a quantum
strong selective direct product property; namely, there are constants `γ > 0` and `k₀ ≥ 1` such
that for all sufficiently small constant `ε > 0`, for any function `f` and any integers
`k₀ ≤ k < m`, `Q_{1−(1−ε)^{γk}}(f^(k,m))` is `Ω(k · Q_ε(f))`.

**Formalization Note.** "For all sufficiently small constant `ε > 0`" is every `ε ∈ (0, 1/10]`;
`Ω` is a constant `α > 0` chosen after `ε` and before `d`, `n`, `Y`, `D`, `f`, `k`, `m`. The range
`k₀ ≤ k ≤ m` contains the printed `k₀ ≤ k < m`. Both sides are worst-case query complexities in
`ℕ∞` (`⊤` if no algorithm exists), compared in `[0, ∞]`. `f^(k,m)` is the selective direct product
of the graph of `f` on `D^m`: the algorithm outputs `k` (copy, value) pairs with pairwise distinct
copies of its choice, and succeeds with probability at least `(1−ε)^{γk}` on every input of
`D^m`. The alphabet `X` is `Z_d`, inputs are `Fin n → Z_d`, and `m`-copy inputs are indexed by
`Fin m × Fin n`. -/
theorem theorem_1_9 :
    ∃ γ : ℝ, 0 < γ ∧ ∃ k₀ : ℕ, 1 ≤ k₀ ∧
      ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 10 →
      ∃ α : ℝ, 0 < α ∧
        ∀ (d n : ℕ) [NeZero d] (Y : Type u) (D : Finset (Fin n → ZMod d))
          (f : (Fin n → ZMod d) → Y) (k m : ℕ), k₀ ≤ k → k ≤ m →
          ENNReal.ofReal (α * k) * (Qfun D f ε : ℝ≥0∞) ≤
            (Qrel (prodDomain D m) (selRel k m (fun x y => f x = y))
              (1 - (1 - ε) ^ (γ * k)) : ℝ≥0∞) := by sorry

end SelectiveDPT
