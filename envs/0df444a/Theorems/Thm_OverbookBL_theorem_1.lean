-- Prove2me | Theorems.Thm_OverbookBL_theorem_1
-- name    : OverbookBL.theorem_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:55:47.590576+00:00
-- url     : https://prove2.me/theorems/8f5d9cec-75fa-4dcc-bc7f-261516d430f7
-- title:
--   Theorem 1 — $\widehat{\mathrm{OPT}}_{\vec A}-\mathcal H_{\vec A}[1]\le M_1$ (corrected: $-V_B$ in (1))
-- statement:
--   There is a constant $M_1$, depending only on the instance, such that for every capacity $B$, horizon $T$ and arrival vector $\vec A$,
--
--   $$
--   \widehat{\mathrm{OPT}}_{\vec A}-\mathcal H_{\vec A}[1]\le M_1,
--   $$
--
--   and in particular $\mathbb E_{\vec A}\big[\widehat{\mathrm{OPT}}_{\vec A}\big]\le M_1+\mathbb E_{\vec A}\big[\mathcal H_{\vec A}[1]\big]$.
--
--   Restricting the clairvoyant to index solutions costs at most a constant on every sample path. This is the first half of the main theorem.
--
--   Differences from the source:
--   - correction: problem (1) printed with + V_B(x⃗[t−1] + x⃗) (p.10) → objective Σⱼ vⱼ(pastⱼ + xⱼ) − V_B(past + x); reason: sign typo: the objective on p.9, Definition 2 (p.12) and the proof of Theorem 1 (p.24) subtract the compensation; with + Lemma 1 is false (k = 1, p₁ = 1, v₁ = 1/2, B = 0, no past, Ñ₁ = 1: x₁ = 1 is optimal, but (ii) needs 1 ≤ 1/2)
--   - encoding: the model of §2 (p.9) with implicit vⱼ ≥ 0, pⱼ > 0 and the tie rule for adjacent types → the structure Instance with explicit 0 ≤ vⱼ, 0 < pⱼ, and the tie rule for every pair i < j; vⱼ < 1 not a separate field; reason: vⱼ is a revenue and qⱼ = vⱼ/pⱼ must be defined; for sorted ratios the pairwise and adjacent tie rules are equivalent; vⱼ < 1 follows from vⱼ < pⱼ ≤ 1; no instance changes
--   - reading: qⱼ < 1 assumed "without loss of generality" (p.10) → qⱼ < 1 for every type, as a field of Instance; reason: the paper's standing assumption for all its results; the one-sentence reduction for qⱼ ≥ 1 is a remark, not a theorem, and is not formalized
--   - encoding: types 1,…,k and periods 1,…,T → Fin k and Fin T (0-based); 1-based period t of H_A⃗[t] kept as a natural-number argument; reason: Lean indexing; same objects
--   - reading: "there exists a constant M₁" → ∃ M₁ chosen before B, T (and everything else); reason: footnote 3, p.12: constant means independent of B and T
-- source:
--   D. Freund and J. Zhao, Overbooking with bounded loss, arXiv:2204.11148v2 (26 Apr 2022), https://arxiv.org/abs/2204.11148v2, Theorem 1, p.14 (proof pp.24–26)

import Definitions.Def_OverbookBL_expectedLoss

namespace OverbookBL

/-- **Theorem 1** (Freund & Zhao, *Overbooking with bounded loss*, arXiv:2204.11148v2, p.14).
There exists a constant `M₁` such that for every capacity `B`, horizon `T` and arrival vector `A⃗`,
`ÔPT_A⃗ − H_A⃗[1] ≤ M₁`, which implies in particular that `E_A⃗[ÔPT_A⃗] ≤ M₁ + E_A⃗[H_A⃗[1]]`.

**Formalization Note** "Constant" means independent of `B` and `T` (footnote 3, p.12), so `M₁` is
chosen before `B`, `T` and `A⃗`. `ÔPT_A⃗` is `OPT` and `H_A⃗[1]` is `clairIdx` (the hybrid objective
in period 1, `Hyb … 1`, which does not depend on the online policy). Expectations are over i.i.d.
arrival sequences with weight `∏ₜ λ_{Aₜ}`. Problem (1) is read with `−V_B`. -/
theorem theorem_1 {k : ℕ} (I : Instance k) : ∃ M₁ : ℝ, (∀ (B T : ℕ) (A : Fin T → Fin k), OPT I B A - clairIdx I B A ≤ M₁) ∧ ∀ B T : ℕ, ∑ A : Fin T → Fin k, seqWeight I A * OPT I B A ≤ M₁ + ∑ A : Fin T → Fin k, seqWeight I A * clairIdx I B A := by sorry

end OverbookBL
