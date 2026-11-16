-- Prove2me | Theorems.Thm_SelectiveDPT_Supplement_theorem_5_10
-- name    : SelectiveDPT.Supplement.theorem_5_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T00:39:15.04888+00:00
-- url     : https://prove2.me/theorems/8f8cd07f-d855-4f48-823f-960ac8a794be
-- title:
--   Theorem 5.10 — $Q_{1-(9/10)^{\gamma k}}(f^{L(k,m)}) \ge \alpha k\, Q_{1/10}(f)$ for every Boolean $f$
-- statement:
--   Fix $\varepsilon = 1/10$. There are constants $\alpha, \gamma > 0$ and an integer $k_0 \ge 1$ such that for every alphabet size $d \ge 1$, every $n$, every domain $D \subseteq X^n$, every Boolean function $f : D \to \{0,1\}$ and all integers $k$ with $k_0 \le k \le m$,
--   $$Q_{1-(1-\varepsilon)^{\gamma k}}\big(f^{L(k,m)}\big) \;\ge\; \alpha k \cdot Q_\varepsilon(f).$$
--
--   Both sides are worst-case query complexities; $f^{L(k,m)}$ asks for a list of at most $2^{m-k}$ vectors in $\{0,1\}^m$ containing $f^{\otimes m}(x)$. This is the precise form of Theorem 1.11.
--
--   Differences from the source:
--   - reading: there are constants α, γ > 0 and an integer k₀ ≥ 1 → α, γ, k₀ chosen before d, n, D, f, k, m; reason: the constants are absolute
--   - generalization: L ∈ (Y^m choose |Y|^{m−k}) (Definition 5.1, lists of exactly |Y|^{m−k} vectors) → lists L ⊆ Y^m with |L|·|Y|^k ≤ |Y|^m (listRel); reason: every list of the exact size qualifies, so the Lean statement covers the source's; the size 'at most |Y|^{m−k}' is the one of the introduction (p.6) and of the proofs (p.46)
--   - encoding: f : D → {0,1} → f : (Fin n → ZMod d) → Bool, read only on D; reason: {0,1} is Bool; values outside D are never read
--   - encoding: inputs x ∈ X^n with |X| = d, a T-query algorithm measuring its work register and post-processing the result → X = ZMod d, inputs Fin n → ZMod d with a Finset domain D, QAlgorithms.QueryAlg with workspace Fin b for any b, a full computational-basis measurement followed by an output map, query complexity in ℕ∞ (⊤ if no algorithm exists) compared in [0, ∞]; reason: relabelling X as Z_d is the paper's own convention (p.9); only the workspace dimension matters; measuring a designated output register is a special output map
-- source:
--   Beame–Kornerup–Whitmeyer, Strong Selective and List-Decoding Direct Product Theorems for Quantum Query Complexity, arXiv:2609.26678, Theorem 5.10, p.47

import Mathlib
import Definitions.Def_SelectiveDPT_Qfun
import Definitions.Def_SelectiveDPT_prodDomain
import Definitions.Def_SelectiveDPT_Supplement_listRel

open scoped ENNReal

namespace SelectiveDPT.Supplement

/-- Theorem 5.10 of arXiv:2609.26678 (Beame–Kornerup–Whitmeyer), p.47: fix `ε = 1/10`. There are
constants `α, γ > 0` and an integer `k₀ ≥ 1` such that for `f : D → {0,1}` where `D ⊆ X^n`, and for
all integers `k` with `k₀ ≤ k ≤ m` we have `Q_{1−(1−ε)^{γk}}(f^{L(k,m)}) ≥ αk · Q_ε(f)`.

**Formalization Note.** `α`, `γ`, `k₀` are chosen before `d`, `n`, `D`, `f`, `k`, `m`. Both sides
are worst-case query complexities (base `Qfun`, `Qrel`) in `ℕ∞`, compared in `[0, ∞]`;
`f^{L(k,m)}` is the list-decoding relation (`listRel`) of the graph of `f` on `D^m`. The exponent
`γk` is real. `{0,1}` is `Bool`. -/
theorem theorem_5_10 :
    ∃ α γ : ℝ, 0 < α ∧ 0 < γ ∧ ∃ k₀ : ℕ, 1 ≤ k₀ ∧
      ∀ (d n : ℕ) [NeZero d] (D : Finset (Fin n → ZMod d))
        (f : (Fin n → ZMod d) → Bool) (k m : ℕ), k₀ ≤ k → k ≤ m →
        ENNReal.ofReal (α * k) * (Qfun D f (1 / 10) : ℝ≥0∞) ≤
          (Qrel (prodDomain D m) (listRel k m (fun x y => f x = y))
            (1 - (1 - 1 / 10 : ℝ) ^ (γ * k)) : ℝ≥0∞) := by sorry

end SelectiveDPT.Supplement
