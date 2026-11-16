-- Prove2me | Theorems.Thm_SelectiveDPT_Supplement_theorem_1_11
-- name    : SelectiveDPT.Supplement.theorem_1_11
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T00:32:20.335342+00:00
-- url     : https://prove2.me/theorems/be4baa46-5468-42f1-830e-9f98f9e4e951
-- title:
--   Theorem 1.11 — every Boolean function satisfies a quantum strong list-decoding direct product theorem
-- statement:
--   There are constants $\gamma > 0$ and $k_0 \ge 1$ such that for every $\varepsilon \in (0, 1/10]$ there is $\alpha > 0$ with the following property. For every alphabet size $d \ge 1$, every $n$, every domain $D \subseteq X^n$, every Boolean function $f : D \to \{0,1\}$ and all integers $k, m$ with $k_0 \le k \le m$,
--   $$Q_{1-(1-\varepsilon)^{\gamma k}}\big(f^{L(k,m)}\big) \;\ge\; \alpha\, k\, Q_\varepsilon(f).$$
--
--   Here $f^{L(k,m)}$ is the list-decoding direct product: on $m$ inputs in $D$ the algorithm outputs a list of at most $2^{m-k}$ vectors in $\{0,1\}^m$ and succeeds when the list contains $(f(x_1), \dots, f(x_m))$. The left side is the worst-case number of queries needed to succeed with probability at least $(1-\varepsilon)^{\gamma k}$ on every input of $D^m$; the right side involves the worst-case bounded-error query complexity of $f$. So fewer than $\alpha k Q_\varepsilon(f)$ queries cannot even narrow the $2^m$ possible answer vectors down to $2^{m-k}$ candidates, except with probability exponentially small in $k$.
--
--   **Formalization Note** $\gamma$ and $k_0$ do not depend on $\varepsilon$; $\alpha$ does.
--
--   Differences from the source:
--   - generalization: for all sufficiently small constant ε > 0 (some threshold ε₀) → every ε ∈ (0, 1/10]; reason: fixing the threshold ε₀ = 1/10 is stronger than ∃ ε₀ and specializes to the source's claim; Theorem 5.10 is the case ε = 1/10; this is the base mission's reading of Theorem 1.9
--   - reading: Q_{1−(1−ε)^{γk}}(f^{L(k,m)}) is Ω(k·Q_ε(f)) → ∃ α > 0 chosen after ε and before d, n, D, f, k, m; reason: ε is a fixed constant, so the constant of Ω may depend on it but on nothing else
--   - generalization: k₀ ≤ k < m → k₀ ≤ k ≤ m; reason: the Lean statement also covers k = m and specializes to k < m; Theorem 5.10 has k ≤ m
--   - generalization: L ∈ (Y^m choose |Y|^{m−k}) (Definition 5.1, lists of exactly |Y|^{m−k} vectors) → lists L ⊆ Y^m with |L|·|Y|^k ≤ |Y|^m (listRel); reason: every list of the exact size qualifies, so the Lean statement covers the source's; the size 'at most |Y|^{m−k}' is the one of the introduction (p.6) and of the proofs (p.46)
--   - encoding: f : D → {0,1} → f : (Fin n → ZMod d) → Bool, read only on D; reason: {0,1} is Bool; values outside D are never read
--   - encoding: inputs x ∈ X^n with |X| = d, a T-query algorithm measuring its work register and post-processing the result → X = ZMod d, inputs Fin n → ZMod d with a Finset domain D, QAlgorithms.QueryAlg with workspace Fin b for any b, a full computational-basis measurement followed by an output map, query complexity in ℕ∞ (⊤ if no algorithm exists) compared in [0, ∞]; reason: relabelling X as Z_d is the paper's own convention (p.9); only the workspace dimension matters; measuring a designated output register is a special output map
-- source:
--   Beame–Kornerup–Whitmeyer, Strong Selective and List-Decoding Direct Product Theorems for Quantum Query Complexity, arXiv:2609.26678, Theorem 1.11, p.7

import Mathlib
import Definitions.Def_SelectiveDPT_Qfun
import Definitions.Def_SelectiveDPT_prodDomain
import Definitions.Def_SelectiveDPT_Supplement_listRel

open scoped ENNReal

namespace SelectiveDPT.Supplement

/-- Theorem 1.11 of arXiv:2609.26678 (Beame–Kornerup–Whitmeyer), p.7: every Boolean output
function satisfies a quantum strong list-decoding direct product property; namely there are
constants `γ > 0` and `k₀ ≥ 1` such that for all sufficiently small constant `ε > 0`, any function
`f : D → {0,1}` where `D ⊆ X^n`, and any integers `k₀ ≤ k < m`, `Q_{1−(1−ε)^{γk}}(f^{L(k,m)})` is
`Ω(k · Q_ε(f))`.

**Formalization Note.** Read exactly as the base mission read Theorem 1.9: "for all sufficiently
small constant `ε > 0`" is every `ε ∈ (0, 1/10]`; `Ω` is a constant `α > 0` chosen after `ε` and
before `d`, `n`, `D`, `f`, `k`, `m`; the range `k₀ ≤ k ≤ m` contains the printed `k₀ ≤ k < m`. Both
sides are worst-case query complexities in `ℕ∞` (base `Qfun`, `Qrel`), compared in `[0, ∞]`.
`{0,1}` is `Bool`. `f^{L(k,m)}` is the list-decoding relation (`listRel`) of the graph of `f` on
`D^m`: a list of at most `2^{m−k}` vectors in `{0,1}^m`, correct iff it contains `f^{⊗m}(x)`. -/
theorem theorem_1_11 :
    ∃ γ : ℝ, 0 < γ ∧ ∃ k₀ : ℕ, 1 ≤ k₀ ∧
      ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 10 →
      ∃ α : ℝ, 0 < α ∧
        ∀ (d n : ℕ) [NeZero d] (D : Finset (Fin n → ZMod d))
          (f : (Fin n → ZMod d) → Bool) (k m : ℕ), k₀ ≤ k → k ≤ m →
          ENNReal.ofReal (α * k) * (Qfun D f ε : ℝ≥0∞) ≤
            (Qrel (prodDomain D m) (listRel k m (fun x y => f x = y))
              (1 - (1 - ε) ^ (γ * k)) : ℝ≥0∞) := by sorry

end SelectiveDPT.Supplement
