-- Prove2me | Theorems.Thm_SingleMachinePrec_IntervalChromatic_theorem_4_3
-- name    : SingleMachinePrec.IntervalChromatic.theorem_4_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T01:29:51.993415+00:00
-- url     : https://prove2.me/theorems/c972fddb-6208-45e2-9059-888826ab7461
-- title:
--   Theorem 4.3 — unbounded chromatic number
-- statement:
--   Let $I_n$ be the canonical interval order on all closed intervals with distinct endpoints in $[n]$, and let $G_{I_n}$ be its graph of ordered incomparable pairs. For every nonnegative integer $k$, there is a threshold $n_0\ge2$ such that
--
--   $$
--   n\ge n_0\quad\Longrightarrow\quad G_{I_n}\text{ is not $k$-colorable}.
--   $$
--
--   Hence the chromatic numbers of these graphs eventually exceed every fixed bound. The paper states the result for integer $k$; negative values are immediate because chromatic numbers are nonnegative.
--
--   **Formalization Note** Colorability is an explicit proper map into `Fin k`. This captures the paper's chromatic inequality for the relevant nonempty graphs and handles $k=0$ without relying on a supremum or infimum convention.
-- source:
--   Ambühl, Mastrolilli, Mutsanas, Svensson, On the Approximability of Single-Machine Scheduling with Precedence Constraints, Math. Oper. Res. 36(4) (2011), p. 658, Theorem 4.3; DOI 10.1287/moor.1110.0512

import Definitions.Def_SingleMachinePrec_IntervalChromatic_CanonicalOrder

namespace SingleMachinePrec.IntervalChromatic

/-- Theorem 4.3, p. 658: no fixed number of colors suffices for all canonical interval orders. -/
theorem theorem_4_3 (k : ℕ) :
    ∃ n₀ : ℕ, 2 ≤ n₀ ∧ ∀ n : ℕ, n₀ ≤ n → ¬ Colorable n k := by sorry

end SingleMachinePrec.IntervalChromatic
