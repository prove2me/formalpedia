-- Prove2me | Theorems.Thm_ParriloTheta_eq_2_3
-- name    : ParriloTheta.eq_2_3
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:28:59.931631+00:00
-- url     : https://prove2.me/theorems/59511db7-65c9-4f10-8498-85cf5ccb6c60
-- title:
--   (2.3) — $\mathcal K^{(0)}_n=\{P+N: P\succeq0,\ N\ge0\}$, and $\mathcal K^{(0)}$-certificates
-- statement:
--   Let $M$ be a real matrix indexed by a finite set. Then
--   1. $M\in\mathcal K^{(0)}_n$ if and only if $M=P+N$ for some positive semidefinite $P$ and some symmetric, entrywise nonnegative $N$;
--   2. $M\in\mathcal K^{(0)}_n$ if and only if $M$ is symmetric and has a $\mathcal K^{(0)}$-certificate, i.e. a matrix $P\succeq0$ with $P\le M$ entrywise and $P_{ii}=M_{ii}$ for all $i$.
--
--   This is Parrilo's description of the zeroth cone; it reduces $\vartheta$-rank $0$ to a semidefinite feasibility problem.
--
--   Differences from the source:
--   - encoding: N ≥ 0 with P + N ∈ Sⁿ → N symmetric and entrywise nonnegative; reason: K⁽⁰⁾ₙ ⊆ Sⁿ, and P + N is symmetric exactly when N is; same sets
--   - encoding: matrices indexed by [n] → matrices indexed by a finite type ι; reason: Lean convention
-- source:
--   Laurent & Vargas, Exactness of Parrilo's conic approximations for copositive matrices and associated low order bounds for the stability number of a graph, arXiv:2109.12876v1, eq. (2.3) and the following paragraph, p.5

import Mathlib
import Definitions.Def_ParriloTheta_InK
import Definitions.Def_ParriloTheta_IsK0Cert

namespace ParriloTheta

/-- **(2.3): Parrilo's description of `K^(0)`, and `K^(0)`-certificates.**
Laurent & Vargas, *Exactness of Parrilo's conic approximations for copositive matrices and
associated low order bounds for the stability number of a graph*, arXiv:2109.12876v1, eq. (2.3) and the paragraph after it, p.5:
"K(0)_n = {P + N : P ⪰ 0, N ≥ 0}. (2.3) Note that in (2.3) we can indeed assume, without loss of
generality, that N_ii = 0 for all i ∈ [n]. We say that P is a K(0)-certificate for M if P ⪰ 0,
P ≤ M and P_ii = M_ii for all i ∈ [n]."

First conjunct: `M ∈ K^(0)` iff `M = P + N` with `P ⪰ 0` and `N` symmetric and entrywise
nonnegative. Second conjunct: `M ∈ K^(0)` iff `M` is symmetric and has a `K^(0)`-certificate.

**Formalization Note.** `N` is required symmetric because `K^(0)_n ⊆ Sⁿ` (1.4): `P + N` is a
matrix of `Sⁿ` exactly when `N` is symmetric. `N ≥ 0` is entrywise (p.4). -/
theorem eq_2_3 {ι : Type*} [Fintype ι] (M : Matrix ι ι ℝ) :
    (InK 0 M ↔ ∃ P N : Matrix ι ι ℝ, M = P + N ∧ P.PosSemidef ∧ N.IsSymm ∧ ∀ i j, 0 ≤ N i j) ∧
    (InK 0 M ↔ M.IsSymm ∧ ∃ P : Matrix ι ι ℝ, IsK0Cert M P) := by sorry

end ParriloTheta
