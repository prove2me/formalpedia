-- Prove2me | Theorems.Thm_OverbookBL_lemma_2
-- name    : OverbookBL.lemma_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:54:05.775773+00:00
-- url     : https://prove2.me/theorems/82bbfd9c-877f-452d-ac7b-819f10b30553
-- title:
--   Lemma 2 — local Lipschitz bound $\delta$ on locally optimal solutions (corrected: $-V_B$ in (1))
-- statement:
--   There exists a constant $\delta\ge1$, depending only on the instance, such that for any capacity $B$, past accepted arrivals $\vec x[t-1]$, (estimated) future arrivals $\widetilde N^f[t]$, any solution $\vec x^\star$ of problem (1) that is locally optimal at $j$ and any type $i$ (with room for one more type-$i$ customer when $i\ne j$), there is $l\in\{0,1,\dots,\delta\}$ such that
--
--   $$
--   \vec x'=\vec x^\star+e_i-l\,e_j
--   $$
--
--   is a solution of (1) that is locally optimal at $j$.
--
--   Accepting one more customer of any type changes a locally optimal number of type-$j$ customers by at most $\delta$. Lemma 6 and Claim 3 apply this bound repeatedly.
--
--   Differences from the source:
--   - correction: problem (1) printed with + V_B(x⃗[t−1] + x⃗) (p.10) → objective Σⱼ vⱼ(pastⱼ + xⱼ) − V_B(past + x); reason: sign typo: the objective on p.9, Definition 2 (p.12) and the proof of Theorem 1 (p.24) subtract the compensation; with + Lemma 1 is false (k = 1, p₁ = 1, v₁ = 1/2, B = 0, no past, Ñ₁ = 1: x₁ = 1 is optimal, but (ii) needs 1 ≤ 1/2)
--   - encoding: the model of §2 (p.9) with implicit vⱼ ≥ 0, pⱼ > 0 and the tie rule for adjacent types → the structure Instance with explicit 0 ≤ vⱼ, 0 < pⱼ, and the tie rule for every pair i < j; vⱼ < 1 not a separate field; reason: vⱼ is a revenue and qⱼ = vⱼ/pⱼ must be defined; for sorted ratios the pairwise and adjacent tie rules are equivalent; vⱼ < 1 follows from vⱼ < pⱼ ≤ 1; no instance changes
--   - reading: qⱼ < 1 assumed "without loss of generality" (p.10) → qⱼ < 1 for every type, as a field of Instance; reason: the paper's standing assumption for all its results; the one-sentence reduction for qⱼ ≥ 1 is a remark, not a theorem, and is not formalized
--   - reading: "x⃗′ = x⃗⋆ + eᵢ − leⱼ is locally optimal at j" for any solution x⃗⋆ → hypothesis x⋆ᵢ < Ñᶠᵢ[t] when i ≠ j, and l ≤ x⋆ⱼ + 𝟙{i=j} in the conclusion (IsLipConst); reason: local optimality is defined for feasible solutions, so x⃗′ must be feasible; for i = j the statement holds with l = 1
-- source:
--   D. Freund and J. Zhao, Overbooking with bounded loss, arXiv:2204.11148v2 (26 Apr 2022), https://arxiv.org/abs/2204.11148v2, Lemma 2, p.13 (proof pp.17–19)

import Definitions.Def_OverbookBL_IsLipConst

namespace OverbookBL

/-- **Lemma 2** (Freund & Zhao, *Overbooking with bounded loss*, arXiv:2204.11148v2, p.13). There
exists a constant `δ ≥ 1` such that for any solution `x⋆` of problem (1) with `Ñᶠ[t]` and `x⃗[t−1]`,
if `x⋆` is locally optimal at `j`, then there is `l ∈ {0, 1, …, δ}` such that
`x⃗′ = x⋆ + eᵢ − l eⱼ` is locally optimal at `j`.

**Formalization Note** The property of `δ` is `IsLipConst I δ`: "`x⃗′` is locally optimal at `j`"
includes that `x⃗′` is a solution of (1), which is why `IsLipConst` assumes `x⋆ᵢ < Ñᶠᵢ[t]` for
`i ≠ j` and requires `l ≤ x⋆ⱼ + 𝟙{i=j}`. `δ` depends only on the instance (it is chosen before the
capacity, the past, the estimate and the solution). -/
theorem lemma_2 {k : ℕ} (I : Instance k) : ∃ δ : ℕ, 1 ≤ δ ∧ IsLipConst I δ := by sorry

end OverbookBL
