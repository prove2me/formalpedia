-- Prove2me | Theorems.Thm_QMCBeyondHK_eq_8
-- name    : QMCBeyondHK.eq_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:38:06.45557+00:00
-- url     : https://prove2.me/theorems/b3883eea-8188-4b01-8056-c3a608f22753
-- title:
--   §3.1, eq. (8) — one Haar function per scale is nonzero at each point, and $1-\varepsilon/2 \le \mu_t \le 1+\varepsilon/2$
-- statement:
--   Let $d \ge 1$, $\varepsilon \in (0,1)$, $n \ge 1$, $\ell = \lceil 10\log_2 n\rceil$ and $N_\ell = (\ell+1)^d$.
--
--   1. For every $x \in [0,1)^d$ and every scale vector $j \in \mathbb N^d$, exactly one Haar function $H_{j,k}$ is nonzero at $x$.
--   2. A Haar function that is nonzero at $x \in [0,1)^d$ takes the value $\pm 1$ there.
--   3. Hence at most $N_\ell$ functions of $\Pi_{\le\ell}$ are nonzero at any $x \in [0,1)^d$.
--   4. For every list $A$ of retained points, the Haar-thinning density (7) built from $A$ satisfies
--   $$
--   1 - \frac{\varepsilon}{2} \le \mu(x) \le 1 + \frac{\varepsilon}{2} \qquad \text{for every } x \in [0,1)^d .
--   $$
--
--   This is what makes (7) an admissible target density of the thinning framework, and the term count behind the per-sample running time of Theorem 1.2.
--
--   Differences from the source:
--   - generalization: μ_t at step t of a run of the strategy → the density (7) built from an arbitrary list A of points; reason: (8) holds for every value of the discrepancies; the retained list A_t of any run is such a list
-- source:
--   Ezeunala, Jha, Jiang, Quasi-Monte Carlo Beyond Hardy–Krause II: (1 + ε)n Samples Suffice, arXiv:2609.10921 (sha256 bc273e88…), §3.1, eq. (8), p.8 (PDF p.10)

import Mathlib
import Definitions.Def_QMCBeyondHK_haarRun

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace QMCBeyondHK

/-- §3.1, eq. (8), printed p.8 (PDF p.10) of Ezeunala, Jha, Jiang, *Quasi-Monte Carlo Beyond
Hardy–Krause II*, arXiv:2609.10921 (sha256 bc273e88…): for every `x ∈ [0,1)^d` and every scale
vector `j`, exactly one Haar function `H_{j,k}` is nonzero at `x`, with value `±1`; hence at most
`N_ℓ` terms of (7) are nonzero at `x`, and `1 − ε/2 ≤ μ_t(x) ≤ 1 + ε/2`.

**Formalization Note** `ℓ = ⌈10 log₂ n⌉`, `N_ℓ = (ℓ+1)^d`; `μ_t` is `density` for an arbitrary list
`A` of retained points. -/
theorem eq_8 (d : ℕ) (hd : 1 ≤ d) (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) (n : ℕ) (hn : 1 ≤ n) :
    (∀ x ∈ cube d, ∀ j : Fin d → ℕ, ∃! H : HaarIdx d, H.j = j ∧ haar H x ≠ 0) ∧
    (∀ x ∈ cube d, ∀ H : HaarIdx d, haar H x ≠ 0 → haar H x = 1 ∨ haar H x = -1) ∧
    (∀ x ∈ cube d, ((lowOrder d (ell n)).filter (fun H => haar H x ≠ 0)).card ≤ Nell d (ell n)) ∧
    (∀ (A : List (Fin d → ℝ)), ∀ x ∈ cube d,
      1 - ε / 2 ≤ density d ε (ell n) A x ∧ density d ε (ell n) A x ≤ 1 + ε / 2) := by sorry

end QMCBeyondHK
