-- Prove2me | Theorems.Thm_SmoothBerr_Supplement_theorem_2_2
-- name    : SmoothBerr.Supplement.theorem_2_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T04:02:02.988546+00:00
-- url     : https://prove2.me/theorems/b27535f9-712d-4f12-a91e-303469c7269c
-- title:
--   Theorem 2.2 — deterministic algorithms need $t\gtrsim n$ matvecs for backward error $1/2$
-- statement:
--   There is a universal constant $c>0$ such that the following holds for every $n$. Let $\Phi$ be a deterministic adaptive matvec algorithm that, given $b\in\mathbb R^n$, computes matvecs with $A$ (and $A^\top$). Suppose that for every invertible $A\in\mathbb R^{n\times n}$ and every $b$, the algorithm halts after at most $t$ matvecs and returns $\tilde x$ with
--   $$
--   (A+\Delta)\tilde x=b\quad\text{for some }\Delta\text{ with }\|\Delta\|_2\le\tfrac12\|A\|_2 .
--   $$
--   Then $t\ge c\,n$.
--
--   Without randomness, backward error $1/2$ on all $n\times n$ systems costs as many matvecs as reading the whole matrix. Randomized algorithms reach backward error $\varepsilon$ with $O(\log(n)/\varepsilon)$ matvecs, so this is a separation between deterministic and randomized matvec algorithms for general linear systems.
--
--   **Formalization Note** The constant $c$ is chosen before $n$, $t$ and the algorithm. The guarantee is required only on invertible matrices.
--
--   Differences from the source:
--   - encoding: an algorithm that computes at most t matvecs with A → a DetMatvecAlg that may query x ↦ Ax and y ↦ Aᵀy and halts within t matvecs (HaltsWithin A b t); reason: the matvec model of p.2 allows both kinds of query
--   - generalization: the algorithm solves every system Ax = b → the guarantee is required only for invertible A (and every b); reason: the hypothesis is weaker, so the theorem is stronger; the proof's hard instances have bounded condition number and are invertible
--   - encoding: x̃ solves (A + Δ)x̃ = b with ‖Δ‖₂ ≤ (1/2)‖A‖₂ → BerrLe A b x̃ (1/2); reason: the same condition; ‖·‖₂ is specNorm
--   - encoding: t ≳ n → ∃ c > 0, before n, t and Φ, with c·n ≤ t; reason: §3, p.4: ≳ hides a universal constant
-- source:
--   Dereziński, Mahoney, Meyer, Musco, From smoothed analysis to backward error: The power of adaptive perturbations (manuscript of 3 Nov 2026, STOC 2027 submission; sha256 9575cd20bc2c854eb092a4950988f7fbef8715adda344a1ba39489bc28b4e58d), Theorem 2.2, p.3

import Mathlib
import Definitions.Def_SmoothBerr_Supplement_BerrLe
import Definitions.Def_SmoothBerr_Supplement_DetMatvecAlg

open Matrix

namespace SmoothBerr.Supplement

/-- **Theorem 2.2 (Deterministic methods cannot achieve small backward error)** (Dereziński, Mahoney, Meyer, Musco, *From smoothed analysis to backward error: The power of adaptive perturbations*, manuscript of 3 Nov 2026, sha256 9575cd20…, Theorem 2.2, p.3).

Any deterministic algorithm that takes a vector `b`, computes at most `t` matvecs with a matrix
`A`, and returns a vector `x̃` that solves `(A + Δ)x̃ = b` with `‖Δ‖₂ ≤ (1/2)‖A‖₂` must use
`t ≳ n` matvecs.

**Formalization Note**
1. `t ≳ n` (§3, p.4): a universal constant `c > 0` is chosen first, before `n`, `t` and the
   algorithm; the conclusion is `c n ≤ t`.
2. Algorithms are deterministic adaptive matvec algorithms (`DetMatvecAlg`) that may query both
   `x ↦ A x` and `y ↦ Aᵀ y`; "at most `t` matvecs" is `HaltsWithin A b t`, and `x̃` is the
   output on the final transcript.
3. The guarantee is required only on invertible `A` (and every `b`), which weakens the
   hypothesis. Backward error `≤ 1/2` is `BerrLe A b x̃ (1/2)` (the min-definition of p.4). -/
theorem theorem_2_2 :
    ∃ c : ℝ, 0 < c ∧
      ∀ (n t : ℕ) (Φ : DetMatvecAlg n),
        (∀ A : Matrix (Fin n) (Fin n) ℝ, IsUnit A.det → ∀ b : Fin n → ℝ,
          Φ.HaltsWithin A b t ∧ BerrLe A b (Φ.outputAt A b t) (1 / 2)) →
        c * n ≤ t := by sorry

end SmoothBerr.Supplement
