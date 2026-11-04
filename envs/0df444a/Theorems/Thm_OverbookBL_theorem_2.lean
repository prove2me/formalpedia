-- Prove2me | Theorems.Thm_OverbookBL_theorem_2
-- name    : OverbookBL.theorem_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:55:36.895395+00:00
-- url     : https://prove2.me/theorems/d1ce4211-e6df-4809-8c1a-a397ee25b6a3
-- title:
--   Theorem 2 — the online index policy's expected loss against the clairvoyant optimum is bounded by a constant (corrected: $-V_B$ in (1))
-- statement:
--   Fix an overbooking instance: $k$ types with arrival probabilities $\lambda_j>0$, revenues $v_j\ge0$, rational show-up probabilities $p_j\in(0,1]$ and critical ratios $q_j=v_j/p_j<1$, ordered by critical ratio. There exists a constant $M$ such that for every capacity $B$, every horizon $T$ and every admissible choice of the optimal index solution in line 6 of Algorithm 1,
--
--   $$
--   \mathbb E_{\vec A}\Big[\widehat{\mathrm{OPT}}_{\vec A}-\mathrm{OBJ}_{\vec A}\Big]\le M .
--   $$
--
--   Here $\widehat{\mathrm{OPT}}_{\vec A}$ is the clairvoyant optimum of problem (1) that knows the arrival counts but not the show-ups, and $\mathrm{OBJ}_{\vec A}$ is the expected objective of the online index policy on $\vec A$. The loss of the policy does not grow with the capacity or the horizon.
--
--   Differences from the source:
--   - correction: problem (1) printed with + V_B(x⃗[t−1] + x⃗) (p.10) → objective Σⱼ vⱼ(pastⱼ + xⱼ) − V_B(past + x); reason: sign typo: the objective on p.9, Definition 2 (p.12) and the proof of Theorem 1 (p.24) subtract the compensation; with + Lemma 1 is false (k = 1, p₁ = 1, v₁ = 1/2, B = 0, no past, Ñ₁ = 1: x₁ = 1 is optimal, but (ii) needs 1 ≤ 1/2)
--   - encoding: the model of §2 (p.9) with implicit vⱼ ≥ 0, pⱼ > 0 and the tie rule for adjacent types → the structure Instance with explicit 0 ≤ vⱼ, 0 < pⱼ, and the tie rule for every pair i < j; vⱼ < 1 not a separate field; reason: vⱼ is a revenue and qⱼ = vⱼ/pⱼ must be defined; for sorted ratios the pairwise and adjacent tie rules are equivalent; vⱼ < 1 follows from vⱼ < pⱼ ≤ 1; no instance changes
--   - reading: qⱼ < 1 assumed "without loss of generality" (p.10) → qⱼ < 1 for every type, as a field of Instance; reason: the paper's standing assumption for all its results; the one-sentence reduction for qⱼ ≥ 1 is a remark, not a theorem, and is not formalized
--   - encoding: types 1,…,k and periods 1,…,T → Fin k and Fin T (0-based); 1-based period t of H_A⃗[t] kept as a natural-number argument; reason: Lean indexing; same objects
--   - reading: line 6 of Algorithm 1: "Find optimal index solution x⃗′" (which one unspecified) → any selection rule sel(t, past, Ñ) returning an optimal index solution locally optimal at its threshold index (IsAdmissibleRule), quantified after the constant; reason: p.21 states that this is the only property assumed of x⃗′; requiring it at every input rather than reachable ones changes no run (a rule admissible on reachable inputs extends to all inputs by exists_admissible)
--   - reading: line 7 of Algorithm 1: x′ⱼ ≥ Nᶠⱼ[t]/2 (prose on p.11: x_j̃ > Ñᶠⱼ[t]/2) → accept iff (x′ⱼ : ℝ) ≥ Ñᶠⱼ[t]/2; reason: the tilde is missing in line 7 (line 6 uses Ñ); the box's ≥ is the definition, as used in the proof of Lemma 3 (p.26)
--   - reading: "there exists a constant M" → ∃ M chosen before B, T (and everything else); reason: footnote 3, p.12: constant means independent of B and T
-- source:
--   D. Freund and J. Zhao, Overbooking with bounded loss, arXiv:2204.11148v2 (26 Apr 2022), https://arxiv.org/abs/2204.11148v2, Theorem 2, p.14

import Definitions.Def_OverbookBL_expectedLoss

namespace OverbookBL

/-- **Theorem 2** (Freund & Zhao, *Overbooking with bounded loss*, arXiv:2204.11148v2, p.14).
There exists a constant `M` such that `E_A⃗[ÔPT_A⃗ − OBJ_A⃗] ≤ M`: the expected additive loss of the
online index policy (Algorithm 1) against the clairvoyant general objective is bounded by a
constant independent of the capacity `B` and the horizon `T`.

**Formalization Note** `M` depends only on the instance (`k`, `λ`, `v`, `p`; footnote 3, p.12:
"constant if they do not depend on `B` or `T`") and is chosen before `B`, `T` and the selection
rule. The selection rule is any rule returning, in line 6, an optimal index solution that is
locally optimal at its threshold index (p.21). The acceptance test is `x′ⱼ ≥ Ñᶠⱼ[t]/2` (line 7),
and `Ñᶠ[t]` includes the current arrival (line 5). Problem (1) is read with `−V_B` (the printed
`+` is a sign typo). `OBJ_A⃗` averages the online objective over the sample `A⃗′`; the outer
expectation is over i.i.d. arrival sequences `A⃗` with weight `∏ₜ λ_{Aₜ}`. The instance assumes
`qⱼ < 1` for every type (p.10). -/
theorem theorem_2 {k : ℕ} (I : Instance k) : ∃ M : ℝ, ∀ (B T : ℕ) (sel : ℕ → (Fin k → ℕ) → (Fin k → ℕ) → (Fin k → ℕ)), IsAdmissibleRule I B sel → expectedLoss I B T sel ≤ M := by sorry

end OverbookBL
