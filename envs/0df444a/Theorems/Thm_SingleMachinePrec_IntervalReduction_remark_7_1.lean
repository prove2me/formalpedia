-- Prove2me | Theorems.Thm_SingleMachinePrec_IntervalReduction_remark_7_1
-- name    : SingleMachinePrec.IntervalReduction.remark_7_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T14:31:22.426721+00:00
-- url     : https://prove2.me/theorems/bbb061b8-2220-447b-9b46-2ab32e153a40
-- title:
--   Remark 7.1 — $p_iw_j$ is 1 or at most $1/k$ on incomparable pairs
-- statement:
--   Let $S$ be the Stage 2 instance with parameter $k>1$. Let $i$ and $j$ be jobs with intervals $[a,b]$ and $[c,d]$ such that $a\le d$. Then
--
--   1. $p_i\le 1/k^{\lceil b\rceil}$ and $w_j\le k^{\lceil c\rceil}$;
--   2. if $i$ and $j$ are incomparable in $I$, then $p_i w_j = 1$ or $p_i w_j\le 1/k$;
--   3. if $p_i w_j\ge k$, then $b<c$, that is, the interval of $i$ lies completely to the left of that of $j$;
--   4. if $p_i w_j = 1$, then $\lceil b\rceil = \lceil c\rceil$.
--
--   The remark is the bookkeeping behind Claim 2: on incomparable pairs, the weights of $G^S_I$ split into "heavy" nodes of weight exactly $1$ and "light" nodes of weight at most $1/k$.
--
--   **Formalization Note** The ceilings are integer valued and the powers $k^{\lceil b\rceil}$ are integer powers of the real $k$ ($\lceil b\rceil=-1$ is possible for $s_0$'s left end). The paper takes $k$ "large"; the statement assumes $k>1$, under which parts 3 and 4 hold (at $k=1$ they fail).
-- source:
--   Ambühl, Mastrolilli, Mutsanas, Svensson, On the Approximability of Single-Machine Scheduling with Precedence Constraints, Math. Oper. Res. 36(4) (2011), p. 662, Remark 7.1

import Mathlib
import Definitions.Def_SingleMachinePrec_IntervalReduction_Instance

namespace SingleMachinePrec.IntervalReduction

/-- Remark 7.1 (p. 662): for jobs `i, j` with intervals `[a, b]` and `[c, d]` and `a ≤ d`,
`p_i ≤ 1/k^⌈b⌉`, `w_j ≤ k^⌈c⌉`; if `i, j` are incomparable then `p_i w_j = 1` or
`p_i w_j ≤ 1/k`; `p_i w_j ≥ k` implies `b < c`; and `p_i w_j = 1` implies `⌈b⌉ = ⌈c⌉`. -/
theorem remark_7_1 {N : ℕ} {G : SimpleGraph (Fin N)} (L : TreeLayout G) (k : ℝ) (hk : 1 < k)
    (x y : Job L) (hxy : left L x ≤ right L y) :
    procTime L k x ≤ 1 / k ^ ⌈right L x⌉ ∧
    weight L k y ≤ k ^ ⌈left L y⌉ ∧
    (Incomparable (prec L) x y →
      procTime L k x * weight L k y = 1 ∨ procTime L k x * weight L k y ≤ 1 / k) ∧
    (k ≤ procTime L k x * weight L k y → right L x < left L y) ∧
    (procTime L k x * weight L k y = 1 → ⌈right L x⌉ = ⌈left L y⌉) := by sorry

end SingleMachinePrec.IntervalReduction
