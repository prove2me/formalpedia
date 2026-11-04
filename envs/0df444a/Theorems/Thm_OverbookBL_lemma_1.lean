-- Prove2me | Theorems.Thm_OverbookBL_lemma_1
-- name    : OverbookBL.lemma_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:52:55.346086+00:00
-- url     : https://prove2.me/theorems/fe82291d-57a3-457d-a5f2-53f74f6b4dfa
-- title:
--   Lemma 1 — local optimality at $j$ iff two tail conditions against $q_j$ (corrected: $-V_B$ in (1))
-- statement:
--   Consider problem (1) with capacity $B$, (estimated) future arrivals $\widetilde N^f[t]$ and past accepted arrivals $\vec x[t-1]$. Let $\vec x^\star$ be a feasible solution and $\vec x=\vec x[t-1]+\vec x^\star$. Then $\vec x^\star$ is locally optimal at $j$ if and only if both
--
--   1. $x^\star_j=\widetilde N^f_j[t]$ or $\ \mathbb P\big[\sum_nX_{n,x_n}\ge B\big]>q_j$, and
--   2. $x^\star_j=0$ or $\ \mathbb P\big[\sum_{n\ne j}X_{n,x_n}+X_{j,x_j-1}\ge B\big]\le q_j$,
--
--   where $q_j=v_j/p_j$ is the critical ratio.
--
--   This is a Littlewood-type rule: accept one more type-$j$ customer exactly while the overflow probability stays at or below the critical ratio. It is the working form of local optimality throughout the paper.
--
--   Differences from the source:
--   - correction: problem (1) printed with + V_B(x⃗[t−1] + x⃗) (p.10) → objective Σⱼ vⱼ(pastⱼ + xⱼ) − V_B(past + x); reason: sign typo: the objective on p.9, Definition 2 (p.12) and the proof of Theorem 1 (p.24) subtract the compensation; with + Lemma 1 is false (k = 1, p₁ = 1, v₁ = 1/2, B = 0, no past, Ñ₁ = 1: x₁ = 1 is optimal, but (ii) needs 1 ≤ 1/2)
--   - encoding: the model of §2 (p.9) with implicit vⱼ ≥ 0, pⱼ > 0 and the tie rule for adjacent types → the structure Instance with explicit 0 ≤ vⱼ, 0 < pⱼ, and the tie rule for every pair i < j; vⱼ < 1 not a separate field; reason: vⱼ is a revenue and qⱼ = vⱼ/pⱼ must be defined; for sorted ratios the pairwise and adjacent tie rules are equivalent; vⱼ < 1 follows from vⱼ < pⱼ ≤ 1; no instance changes
--   - reading: qⱼ < 1 assumed "without loss of generality" (p.10) → qⱼ < 1 for every type, as a field of Instance; reason: the paper's standing assumption for all its results; the one-sentence reduction for qⱼ ≥ 1 is a remark, not a theorem, and is not formalized
--   - encoding: X_{j,x_j−1} → the vector x − eⱼ with ℕ subtraction; reason: only read when x⋆ⱼ > 0, where it does not truncate
-- source:
--   D. Freund and J. Zhao, Overbooking with bounded loss, arXiv:2204.11148v2 (26 Apr 2022), https://arxiv.org/abs/2204.11148v2, Lemma 1, p.13 (proof pp.15–17)

import Definitions.Def_OverbookBL_IsLocOpt

namespace OverbookBL

/-- **Lemma 1** (Freund & Zhao, *Overbooking with bounded loss*, arXiv:2204.11148v2, p.13).
For a solution `x⋆ ≤ Ñᶠ[t]` of problem (1) with (estimated) future arrivals `Nf = Ñᶠ[t]` and past
accepted arrivals `past = x⃗[t−1]`, let `x = past + x⋆`. Then `x⋆` is locally optimal at `j` if
and only if
(i) `x⋆ⱼ = Ñᶠⱼ[t]` or `P[∑ₙ X_{n,xₙ} ≥ B] > qⱼ`, and
(ii) `x⋆ⱼ = 0` or `P[∑_{n≠j} X_{n,xₙ} + X_{j,xⱼ−1} ≥ B] ≤ qⱼ`,
where `qⱼ = vⱼ/pⱼ`.

**Formalization Note** Problem (1) is read with `−V_B` (the printed `+` is a sign typo). In (ii)
the vector `x − eⱼ` uses `ℕ` subtraction; it is only relevant when `x⋆ⱼ > 0`, where it does not
truncate. -/
theorem lemma_1 {k : ℕ} (I : Instance k) (B : ℕ) (past Nf x : Fin k → ℕ) (hx : x ≤ Nf) (j : Fin k) : IsLocOpt I B past Nf x j ↔ ((x j = Nf j ∨ I.v j / I.p j < tailProb I.p B (past + x)) ∧ (x j = 0 ∨ tailProb I.p B (past + x - Pi.single j 1) ≤ I.v j / I.p j)) := by sorry

end OverbookBL
