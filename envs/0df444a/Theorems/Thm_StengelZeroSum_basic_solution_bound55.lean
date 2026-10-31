-- Prove2me | Theorems.Thm_StengelZeroSum_basic_solution_bound55
-- name    : StengelZeroSum.basic_solution_bound55
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:04:27.667+00:00
-- url     : https://prove2.me/theorems/817446cd-6fc3-46ac-9400-a2a8cecff068
-- title:
--   Proof of Theorem 7(c) — basic solutions of (58) satisfy $\mathbf1^\top z+1\le\ell!\,\ell\,\alpha^\ell\beta^{\ell^2+\ell}+1$
-- statement:
--   Let $A\in\mathbb Q^{m\times n}$, $b\in\mathbb Q^m$, $c\in\mathbb Q^n$, let $\alpha$ be the largest absolute value of a numerator and $\beta$ the largest denominator among the entries of $A$, $b$, $c$, and let $\ell=m+n+1$. Let $C$, $d$ be as in (57). Then every basic feasible solution $(z,w)$ of (58) satisfies
--
--   $$
--   \mathbf1^\top z+1\le \ell!\,\ell\,\alpha^\ell\beta^{\ell^2+\ell}+1 .
--   $$
--
--   Hence condition (59) of Theorem 8 holds for a basic minimizer with $M$ as in (55); this is how the paper proves Theorem 7(c).
--
--   **Formalization Note** "Basic" for the inequality system (58) is the paper's convention: basic for the slack form. The rational data are cast to real numbers; $\alpha$ and $\beta$ use reduced fractions.
--
--   Differences from the source:
--   - generalization: a basic feasible solution that minimizes w subject to (58) → every basic feasible solution of (58); reason: the rescaling and Cramer argument bounds every basic solution; minimizers are a special case
--   - reading: the numerators and denominators of these numbers → numerators and denominators of the reduced fractions (Rat.num, Rat.den); reason: any other representation has larger α and β, hence a larger bound, which the reduced-form bound implies
--   - encoding: a basic feasible solution of the inequality system (58) → Feasible58 and IsBasic58 (basic for the slack form); reason: the convention of the paper for inequalities, p.20
-- source:
--   von Stengel, Zero-Sum Games and Linear Programming Duality, arXiv:2205.11196v6, proof of Theorem 7(c), pp.23–24

import Mathlib
import Definitions.Def_StengelZeroSum_C57
import Definitions.Def_StengelZeroSum_d57
import Definitions.Def_StengelZeroSum_Feasible58
import Definitions.Def_StengelZeroSum_IsBasic58
import Definitions.Def_StengelZeroSum_bound55

open Matrix

namespace StengelZeroSum

/-- **Basic feasible solutions of (58) satisfy (59) with the `M` of (55)**,
von Stengel, *Zero-Sum Games and Linear Programming Duality*, arXiv:2205.11196v6, proof of
Theorem 7(c), pp.23–24 (rescaling the rational system to an integral one, "which shows (55)").

Let `A, b, c` have rational entries, let `C`, `d` be as in (57), and let `α`, `β`, `ℓ = m + n + 1`
be as in Theorem 7(c). Every basic feasible solution `(z, w)` of (58) satisfies
`1⊤z + 1 ≤ ℓ! ℓ α^ℓ β^(ℓ²+ℓ) + 1`.

**Formalization Note** "Basic" for the inequality system (58) is the paper's convention of p.20,
`IsBasic58`: basic for the slack form `[C −1 I; d⊤ −1 I](z, w, p) = (d, 0)`. The rational data
`Aq, bq, cq` are cast to `ℝ` entrywise; `α`, `β` use reduced numerators and denominators
(`bound55`). `m, n > 0` is the paper's standing assumption (p.4). -/
theorem basic_solution_bound55 {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (Aq : Matrix (Fin m) (Fin n) ℚ) (bq : Fin m → ℚ) (cq : Fin n → ℚ)
    (z : Fin m ⊕ Fin n → ℝ) (w : ℝ)
    (hfeas : Feasible58 (C57 (Aq.map (Rat.cast : ℚ → ℝ)))
      (d57 (fun i => (bq i : ℝ)) fun j => (cq j : ℝ)) z w)
    (hbasic : IsBasic58 (C57 (Aq.map (Rat.cast : ℚ → ℝ)))
      (d57 (fun i => (bq i : ℝ)) fun j => (cq j : ℝ)) z w) :
    ∑ i, z i + 1 ≤ bound55 Aq bq cq := by sorry

end StengelZeroSum
