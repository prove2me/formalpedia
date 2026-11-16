-- Prove2me | Theorems.Thm_SmoothBerr_Supplement_theorem_4_3
-- name    : SmoothBerr.Supplement.theorem_4_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T04:01:30.328128+00:00
-- url     : https://prove2.me/theorems/9bd51c1d-bedd-4c45-8ee4-ac24b2f61ca6
-- title:
--   Theorem 4.3 — deterministic backward-error solvers need $\gtrsim\min\{\log(\kappa)/\varepsilon,n\}$ matvecs (corrected: the $\varepsilon$-range of Theorem 4.6)
-- statement:
--   There are universal constants such that the following holds whenever $n\gtrsim1$, $\kappa\gtrsim1$ and $\kappa^{-0.1}\lesssim\varepsilon\lesssim1$. Let $\Phi$ be a deterministic adaptive matvec algorithm (queries $x\mapsto Ax$ and $y\mapsto A^\top y$). If for every invertible $A\in\mathbb R^{n\times n}$ with $\mathrm{cond}(A)\le\kappa$ and every $b$ the algorithm halts after at most $t$ matvecs and returns $\tilde x$ with $\mathrm{berr}(A,b,\tilde x)\le\varepsilon$, then
--   $$
--   t\ \gtrsim\ \min\Bigl\{\frac{\log\kappa}{\varepsilon},\,n\Bigr\}.
--   $$
--
--   This matches the $O(\log(\kappa)/\varepsilon)$ upper bound of Dereziński, Nakatsukasa and Rebrova: deterministic matvec algorithms cannot avoid a dependence on the condition number, although backward error is by definition insensitive to ill-conditioning.
--
--   **Formalization Note** All constants ($n\ge N_0$, $\kappa\ge K_0$, $\kappa^{-0.1}\le a\varepsilon$, $\varepsilon\le b'$, and the constant $c$ of the conclusion) are chosen first, before $n$, $\kappa$, $\varepsilon$, $t$ and the algorithm.
--
--   Differences from the source:
--   - correction: no range on n, κ, ε → n ≥ N₀, κ ≥ K₀, κ^{−0.1} ≤ a·ε, ε ≤ b' (Theorem 4.6's hypotheses n ≳ 1, κ ≳ 1, κ^{−0.1} ≲ ε ≲ 1, constants chosen first); reason: as printed the claim is false for ε ≪ 1/κ: conjugate gradient on the normal equations is deterministic and reaches relative residual η, hence backward error ≤ η/(1 − η), with O(κ log(1/η)) matvecs; for ε = κ⁻² and n ≥ κ² log κ this is below c·min{log κ/ε, n} = c κ² log κ once κ is large; the paper proves Theorem 4.3 through Theorem 4.6, which carries these hypotheses
--   - encoding: linear systems of condition number cond(A) ≤ κ → CondLe A κ: A invertible and specNorm A ≤ κ·sMin A; reason: cond(A) = σ_max/σ_min (p.4) is defined only for invertible A
--   - encoding: a deterministic matvec algorithm using ≳ min{log(κ)/ε, n} matvecs in the worst case → a DetMatvecAlg (queries with A and Aᵀ) halting within t matvecs with BerrLe … ε on every such (A, b) has c·min{log κ/ε, n} ≤ t; reason: the worst-case count is the least uniform bound t
-- source:
--   Dereziński, Mahoney, Meyer, Musco, From smoothed analysis to backward error: The power of adaptive perturbations (manuscript of 3 Nov 2026, STOC 2027 submission; sha256 9575cd20bc2c854eb092a4950988f7fbef8715adda344a1ba39489bc28b4e58d), Theorem 4.3, p.6

import Mathlib
import Definitions.Def_SmoothBerr_Supplement_BerrLe
import Definitions.Def_SmoothBerr_Supplement_CondLe
import Definitions.Def_SmoothBerr_Supplement_DetMatvecAlg

open Matrix

namespace SmoothBerr.Supplement

/-- **Theorem 4.3 (Deterministic backward error solvers depend on the condition number)** (Dereziński, Mahoney, Meyer, Musco, *From smoothed analysis to backward error: The power of adaptive perturbations*, manuscript of 3 Nov 2026, sha256 9575cd20…, Theorem 4.3, p.6) (corrected: the ε-range of Theorem 4.6).

Every deterministic matvec algorithm that can solve any linear system `Ax = b` of condition number
`cond(A) ≤ κ` to backward error `ε` must use `≳ min{log(κ)/ε, n}` matvecs in the worst case.

**Formalization Note**
1. Correction: the page states no range for `ε`, and for `ε ≪ 1/κ` the claim is false (conjugate
   gradient on the normal equations reaches relative residual, hence backward error, `ε` in
   `O(κ log(1/ε))` deterministic matvecs, which for `ε = κ⁻²` and `n ≥ κ² log κ` is below
   `c κ² log κ` once `κ` is large). The hypotheses `n ≳ 1`, `κ ≳ 1`, `κ^{−0.1} ≲ ε ≲ 1` of
   Theorem 4.6, through which the paper proves this theorem, are added.
2. Every `≲`/`≳` is a universal constant chosen first (`N₀, K₀, a, b', c`), before `n`, `κ`,
   `ε`, `t` and the algorithm.
3. The algorithm may query `A` and `Aᵀ`; "in the worst case" means: if it halts within `t`
   matvecs with backward error `≤ ε` on every invertible `A` with `‖A‖₂ ≤ κ σ_min(A)` (`CondLe`)
   and every `b`, then `c · min{log κ/ε, n} ≤ t`. -/
theorem theorem_4_3 :
    ∃ N₀ K₀ a b' c : ℝ, 0 < a ∧ 0 < b' ∧ 0 < c ∧
      ∀ (n : ℕ) (κ ε : ℝ), N₀ ≤ n → K₀ ≤ κ → κ ^ (-(1 / 10 : ℝ)) ≤ a * ε → ε ≤ b' →
        ∀ (t : ℕ) (Φ : DetMatvecAlg n),
          (∀ A : Matrix (Fin n) (Fin n) ℝ, CondLe A κ → ∀ b : Fin n → ℝ,
            Φ.HaltsWithin A b t ∧ BerrLe A b (Φ.outputAt A b t) ε) →
          c * min (Real.log κ / ε) (n : ℝ) ≤ t := by sorry

end SmoothBerr.Supplement
