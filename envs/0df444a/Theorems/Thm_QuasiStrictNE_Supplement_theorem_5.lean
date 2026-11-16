-- Prove2me | Theorems.Thm_QuasiStrictNE_Supplement_theorem_5
-- name    : QuasiStrictNE.Supplement.theorem_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T05:44:39.692472+00:00
-- url     : https://prove2.me/theorems/d7cac53d-4ec8-406b-bb3f-69d60d71752f
-- title:
--   Theorem 5 (Norde), p.10 — every bimatrix game has a quasi-strict Nash equilibrium
-- statement:
--   Every bimatrix game has a quasi-strict Nash equilibrium. Precisely, let $m, n \ge 1$ and let $A, B \in \mathbb R^{m\times n}$ be the payoff matrices of player 1 and player 2. Then there are mixed strategies $x \in \Delta_m$ and $y \in \Delta_n$ with
--
--   $$
--   \operatorname{supp}(x) = BR_1(y) \qquad\text{and}\qquad \operatorname{supp}(y) = BR_2(x).
--   $$
--
--   The theorem is due to Norde (1999). The paper gives a new proof of it (pp.11–13), using best-response complexes, a piecewise-linear self-map of $\Delta_m \times \Delta_n$ and Brouwer's fixed-point theorem. The same construction yields the PPAD membership in Theorem 1.
--
--   **Formalization Note** `IsQSNE` is the base definition of Definition 1. The hypotheses $m, n \ge 1$ are part of Definition 1: the strategy sets are $[m]$ and $[n]$, and mixed strategies lie in $\Delta_m$, $\Delta_n$, which the paper defines for $k \ge 1$ (for $k = 0$ the simplex is empty). Payoffs are real, as in Definition 1.
--
--   Differences from the source:
--   - encoding: pure strategy sets [m] = {1,…,m}, [n] = {1,…,n} → Fin m, Fin n (0-based); reason: Lean convention, same games
--   - encoding: "every bimatrix game" (Definition 1: Δk defined for k ≥ 1) → hypotheses 1 ≤ m, 1 ≤ n; reason: excludes only m = 0 or n = 0, where Δ0 is empty and no mixed strategy exists, which the paper never considers
-- source:
--   Hansen & Nie, On Existence and Computational Complexity of Quasi-strict Equilibria, arXiv:2611.06350 (preprint, sha256 c265dace…), Theorem 5, p.10 (proof pp.11–13)

import Mathlib
import Definitions.Def_QuasiStrictNE_IsQSNE

set_option autoImplicit false

namespace QuasiStrictNE.Supplement

/-- **Theorem 5 (Norde)** (Hansen & Nie, *On Existence and Computational Complexity of Quasi-strict
Equilibria*, arXiv:2611.06350, Theorem 5, p.10, proved on pp.11–13: "Every bimatrix game has a
quasi-strict Nash equilibrium").

For all `m, n ≥ 1` and all real `m × n` payoff matrices `A` (player 1) and `B` (player 2) there are
mixed strategies `x ∈ Δm`, `y ∈ Δn` with `supp x = BR1(y)` and `supp y = BR2(x)`.

**Formalization Note** `IsQSNE` is the base definition (Definition 1, p.4). `m, n ≥ 1` is part of
Definition 1 (`M = [m]`, `N = [n]`, mixed strategies in `Δm`, `Δn`, which are empty for `0`). Payoffs
are real, as in Definition 1. -/
theorem theorem_5 {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n) (A B : Matrix (Fin m) (Fin n) ℝ) :
    ∃ (x : Fin m → ℝ) (y : Fin n → ℝ), QuasiStrictNE.IsQSNE A B x y := by sorry

end QuasiStrictNE.Supplement
