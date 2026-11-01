-- Prove2me | Theorems.Thm_RecoveringBandits_lemma_2
-- name    : RecoveringBandits.lemma_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T07:56:27.551997+00:00
-- url     : https://prove2.me/theorems/f628849a-c392-4365-bb94-5a5434beb18a
-- title:
--   Lemma 2: $\mathrm{UB}_R[K]\cdot T\ge\mathrm{OPT}$, and (3) has an optimal solution of the form $0$ or $1/d^{(k)}_i$ in all but one coordinate
-- statement:
--   Let the instance be admissible and $K\ge0$. Then
--
--   1. for every $T\ge1$, $\ \mathrm{OPT}_R[K,T]\le T\cdot\mathrm{UB}_R[K]$: the optimal value of (3) is an upper bound on that of the offline problem;
--   2. problem (3) has an optimal solution $x^*$ such that $x^*_i\le 1/d^{(1)}_i$ for every $i$, and $x^*_i\in\{0\}\cup\{1/d^{(k)}_i\}_{k\ge1}$ for all $i$ but at most one.
--
--   The first part makes $\mathrm{UB}_R[K]\cdot T$ a benchmark for every policy; the second says an optimal fractional plan pulls almost every arm either never or exactly once every $d^{(k)}_i$ periods, which is the form of a purely periodic policy.
--
--   Differences from the source:
--   - generalization: OPT maximizes over J_i ∈ [T] (every arm pulled at least once) → OPT also allows J_i = 0; reason: the Lean maximum is over a larger set, so the bound implies the paper's
--   - generalization: K a positive integer with K ≤ N (§2) → any natural number K; reason: the statement holds for every K ≥ 0; it specializes to 1 ≤ K ≤ N
--   - encoding: for at least all i ∈ [N] but one → at most one index violates the membership; reason: same meaning for N ≥ 1, and well defined for N = 0
-- source:
--   Simchi-Levi–Zheng–Zhu, Offline Planning and Online Learning under Recovering Rewards, arXiv:2106.14813v2, Lemma 2, p.11

import Mathlib
import Definitions.Def_RecoveringBandits_Admissible
import Definitions.Def_RecoveringBandits_OPT
import Definitions.Def_RecoveringBandits_UB
import Definitions.Def_RecoveringBandits_Lemma2Prop

namespace RecoveringBandits

/-- **Lemma 2**, Simchi-Levi–Zheng–Zhu, arXiv:2106.14813v2, Lemma 2, p.11 (PDF p.11): the optimal
objective value of (3), `UB_R[K]·T`, is an upper bound on that of the offline problem (1).
Further, problem (3) has an optimal solution `{x*_i}` such that `x*_i ≤ 1/d^{(1)}_i` for all
`i ∈ [N]`, and for at least all `i ∈ [N]` but one, `x*_i ∈ {0} ∪ {1/d^{(k)}_i}_{k ≥ 1}`.

**Formalization Note.** The existence of an optimal solution of (3) is part of the conclusion,
not assumed. `OPT` allows arms that are never pulled (`J_i = 0`), so it is at least the paper's
maximum over `J_i ∈ [T]`. -/
theorem lemma_2 {N : ℕ} (R : Fin N → ℕ → ℝ) (Rmax : ℝ) (hR : Admissible R Rmax) (K : ℕ) :
    (∀ T : ℕ, 1 ≤ T → OPT R K T ≤ (T : ℝ) * UB R K) ∧
    ∃ xstar : Fin N → ℝ, IsOpt3 R K xstar ∧ Lemma2Prop R xstar := by sorry

end RecoveringBandits
