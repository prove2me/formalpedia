-- Prove2me | Theorems.Thm_OverbookBL_exists_admissible
-- name    : OverbookBL.exists_admissible
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:53:32.960648+00:00
-- url     : https://prove2.me/theorems/731784a7-c178-46e2-be3c-9907ccdb5920
-- title:
--   p.21 — an optimal index solution locally optimal at its threshold index exists (corrected: $-V_B$ in (1))
-- statement:
--   For every capacity $B$, past accepted arrivals $\vec x[t-1]$ and (estimated) future arrivals $\widetilde N$, problem (1) has an optimal index solution (optimal among index solutions) that is locally optimal at its threshold index, the smallest index with the index-solution property.
--
--   Consequently the solution required in line 6 of Algorithm 1, under the property the analysis assumes of it, always exists, and the class of admissible selection rules in the main theorem is nonempty.
--
--   Differences from the source:
--   - correction: problem (1) printed with + V_B(x⃗[t−1] + x⃗) (p.10) → objective Σⱼ vⱼ(pastⱼ + xⱼ) − V_B(past + x); reason: sign typo: the objective on p.9, Definition 2 (p.12) and the proof of Theorem 1 (p.24) subtract the compensation; with + Lemma 1 is false (k = 1, p₁ = 1, v₁ = 1/2, B = 0, no past, Ñ₁ = 1: x₁ = 1 is optimal, but (ii) needs 1 ≤ 1/2)
--   - encoding: the model of §2 (p.9) with implicit vⱼ ≥ 0, pⱼ > 0 and the tie rule for adjacent types → the structure Instance with explicit 0 ≤ vⱼ, 0 < pⱼ, and the tie rule for every pair i < j; vⱼ < 1 not a separate field; reason: vⱼ is a revenue and qⱼ = vⱼ/pⱼ must be defined; for sorted ratios the pairwise and adjacent tie rules are equivalent; vⱼ < 1 follows from vⱼ < pⱼ ≤ 1; no instance changes
--   - reading: qⱼ < 1 assumed "without loss of generality" (p.10) → qⱼ < 1 for every type, as a field of Instance; reason: the paper's standing assumption for all its results; the one-sentence reduction for qⱼ ≥ 1 is a remark, not a theorem, and is not formalized
--   - reading: "there exists an index solution that is locally optimal at the threshold index" → there exists an optimal index solution locally optimal at its smallest threshold index; reason: the sentence concerns the optimal index solution x⃗′ of the policy (same paragraph); a non-optimal index solution would not serve line 6
-- source:
--   D. Freund and J. Zhao, Overbooking with bounded loss, arXiv:2204.11148v2 (26 Apr 2022), https://arxiv.org/abs/2204.11148v2, p.21, "we are guaranteed that there exists an index solution that is locally optimal at the threshold index"

import Definitions.Def_OverbookBL_IsAdmissible

namespace OverbookBL

/-- **Existence of an admissible index solution** (Freund & Zhao, *Overbooking with bounded
loss*, arXiv:2204.11148v2, p.21, "we are guaranteed that there exists an index solution that is
locally optimal at the threshold index"). For every capacity `B`, past accepted arrivals `past`
and (estimated) future arrivals `Nf`, problem (1) has an optimal index solution that is locally
optimal at its (smallest) threshold index. In particular the solution required in line 6 of
Algorithm 1 exists.

**Formalization Note** Problem (1) is read with `−V_B`. "Optimal index solution" means optimal
among index solutions (`IsOptIndex`). -/
theorem exists_admissible {k : ℕ} (I : Instance k) (B : ℕ) (past Nf : Fin k → ℕ) : ∃ x : Fin k → ℕ, IsAdmissible I B past Nf x := by sorry

end OverbookBL
