-- Prove2me | Theorems.Thm_ShuffleDecoys_Hierarchy_theorem_3_2
-- name    : ShuffleDecoys.Hierarchy.theorem_3_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T22:23:16.731572+00:00
-- url     : https://prove2.me/theorems/e03960a8-f45e-4f78-b51a-119beac31c4c
-- title:
--   Theorem 3.2 — message-independent integer noise leaks I(M; T) ≥ 9p(1 − p)/(128(σ_y + 1)²)
-- statement:
--   Let $M\sim P$ take values in a finite alphabet $\mathcal Y$, and let $S=(S_y)_{y\in\mathcal Y}$ be an integer-valued random vector independent of $M$. Set $T=e_M+S$, where $e_m$ is the unit vector indexed by $m$. For any $y\in\mathcal Y$ with $p:=P(y)\in(0,1)$ such that $\sigma_y^2:=\operatorname{Var}(S_y)<\infty$,
--   $$I(M;T)\ \ge\ \frac{9p(1-p)}{128(\sigma_y+1)^2}\quad\text{(nats)}.$$
--   The noise may be correlated across coordinates and unbounded; only the variance of the single count $S_y$ enters.
--
--   Differences from the source:
--   - encoding: random vector $S$ independent of $M$ → its law `S : PMF (Y → ℤ)`, joint law of $(M,T)$ = `noiseJoint P S` $=\sum_mP(m)\,\delta_m\otimes\mathrm{Law}(e_m+S)$; reason: independence means exactly this joint law.
--   - encoding: $\operatorname{Var}(S_y)<\infty$ → `HasFiniteVar` of the coordinate law, $\sigma_y=\sqrt{\texttt{pmfVar}}$; reason: same condition and same $\sigma_y$.
-- source:
--   Su, Cheng, Wang, The Information-Theoretic Limits of Hiding Among Decoys in the Shuffle Model, STOC 2027 submission (manuscript sha256 445baceb…), p. 16, Theorem 3.2

import Mathlib
import Definitions.Def_ShuffleDecoys_Hierarchy_Info
import Definitions.Def_ShuffleDecoys_Hierarchy_Model

open scoped ENNReal

namespace ShuffleDecoys.Hierarchy

/-- Theorem 3.2: for `M ∼ P` on a finite alphabet `Y` and an integer noise vector `S` (law `S`)
independent of `M`, `T = e_M + S`; for every `y` with `p = P(y) ∈ (0, 1)` and
`σ_y² = Var(S_y) < ∞`, `I(M; T) ≥ 9p(1 − p)/(128(σ_y + 1)²)` (nats). -/
theorem theorem_3_2 {Y : Type*} [Fintype Y] [DecidableEq Y] (P : PMF Y) (S : PMF (Y → ℤ))
    (y : Y) (hp0 : 0 < (P y).toReal) (hp1 : (P y).toReal < 1)
    (hvar : HasFiniteVar (S.map fun s => s y)) :
    ENNReal.ofReal (9 * (P y).toReal * (1 - (P y).toReal) /
        (128 * (Real.sqrt (pmfVar (S.map fun s => s y)) + 1) ^ 2)) ≤
      mutualInfo (noiseJoint P S) := by sorry

end ShuffleDecoys.Hierarchy
