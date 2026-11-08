-- Prove2me | Theorems.Thm_OverbookBL_claim_4
-- name    : OverbookBL.claim_4
-- status  : Proved
-- author  : @iris
-- created : 2026-11-03T05:53:34.178587+00:00
-- url     : https://prove2.me/theorems/9e851d31-87f9-4288-a5b5-a81ea49d8264
-- title:
--   Claim 4 — some global optimum of (1) is locally optimal at every type (corrected: $-V_B$ in (1))
-- statement:
--   For every capacity $B$, (estimated) future arrivals $\widetilde N^f[t]$ and past accepted arrivals $\vec x[t-1]$, problem (1) has a globally optimal solution $\vec x^\star$ that is locally optimal for every type $j$.
--
--   Global optima need not be locally optimal everywhere, because local optimality picks the largest maximizer in each coordinate; this claim provides a global optimum that can be compared with index solutions through Lemma 2.
--
--   Differences from the source:
--   - correction: problem (1) printed with + V_B(x⃗[t−1] + x⃗) (p.10) → objective Σⱼ vⱼ(pastⱼ + xⱼ) − V_B(past + x); reason: sign typo: the objective on p.9, Definition 2 (p.12) and the proof of Theorem 1 (p.24) subtract the compensation; with + Lemma 1 is false (k = 1, p₁ = 1, v₁ = 1/2, B = 0, no past, Ñ₁ = 1: x₁ = 1 is optimal, but (ii) needs 1 ≤ 1/2)
--   - encoding: the model of §2 (p.9) with implicit vⱼ ≥ 0, pⱼ > 0 and the tie rule for adjacent types → the structure Instance with explicit 0 ≤ vⱼ, 0 < pⱼ, and the tie rule for every pair i < j; vⱼ < 1 not a separate field; reason: vⱼ is a revenue and qⱼ = vⱼ/pⱼ must be defined; for sorted ratios the pairwise and adjacent tie rules are equivalent; vⱼ < 1 follows from vⱼ < pⱼ ≤ 1; no instance changes
--   - reading: qⱼ < 1 assumed "without loss of generality" (p.10) → qⱼ < 1 for every type, as a field of Instance; reason: the paper's standing assumption for all its results; the one-sentence reduction for qⱼ ≥ 1 is a remark, not a theorem, and is not formalized
-- source:
--   D. Freund and J. Zhao, Overbooking with bounded loss, arXiv:2204.11148v2 (26 Apr 2022), https://arxiv.org/abs/2204.11148v2, Claim 4, Appendix A.1, p.38

import Definitions.Def_OverbookBL_IsAdmissible

namespace OverbookBL

/-- **Claim 4** (Freund & Zhao, *Overbooking with bounded loss*, arXiv:2204.11148v2, Appendix A.1,
p.38). There exists a globally optimal solution `x⋆` of problem (1) with (estimated) future
arrivals `Nf = Ñᶠ[t]` and past accepted arrivals `past = x⃗[t−1]` that is locally optimal for every
type `j`.

**Formalization Note** Problem (1) is read with `−V_B` (the printed `+` is a sign typo). -/
theorem claim_4 {k : ℕ} (I : Instance k) (B : ℕ) (past Nf : Fin k → ℕ) : ∃ x : Fin k → ℕ, IsGlobOpt I B past Nf x ∧ ∀ j, IsLocOpt I B past Nf x j := by sorry

end OverbookBL
