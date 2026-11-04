-- Prove2me | Theorems.Thm_OverbookBL_lemma_3
-- name    : OverbookBL.lemma_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:56:02.170016+00:00
-- url     : https://prove2.me/theorems/7cb6e7b6-6237-4ac8-b838-9e342539d71e
-- title:
--   Lemma 3 — $\sum_{t=2}^T P[\mathcal H_{\vec A}[t-1]-\mathcal H_{\vec A}[t]>0]\le M_2$ (corrected: $-V_B$ in (1))
-- statement:
--   There is a constant $M_2$, depending only on the instance, such that for every capacity $B$, horizon $T$ and admissible selection rule of the online index policy,
--
--   $$
--   \sum_{t=2}^T\mathbb P\big[\mathcal H_{\vec A}[t-1]-\mathcal H_{\vec A}[t]>0\big]\le M_2 ,
--   $$
--
--   where the probability is over the arrival sequence $\vec A$ and the policy's sample $\vec A'$.
--
--   The hybrid objective decreases only in periods where the online decision disagrees with the clairvoyant index solution, and the expected number of such periods is bounded. This is the second half of the main theorem.
--
--   Differences from the source:
--   - correction: problem (1) printed with + V_B(x⃗[t−1] + x⃗) (p.10) → objective Σⱼ vⱼ(pastⱼ + xⱼ) − V_B(past + x); reason: sign typo: the objective on p.9, Definition 2 (p.12) and the proof of Theorem 1 (p.24) subtract the compensation; with + Lemma 1 is false (k = 1, p₁ = 1, v₁ = 1/2, B = 0, no past, Ñ₁ = 1: x₁ = 1 is optimal, but (ii) needs 1 ≤ 1/2)
--   - encoding: the model of §2 (p.9) with implicit vⱼ ≥ 0, pⱼ > 0 and the tie rule for adjacent types → the structure Instance with explicit 0 ≤ vⱼ, 0 < pⱼ, and the tie rule for every pair i < j; vⱼ < 1 not a separate field; reason: vⱼ is a revenue and qⱼ = vⱼ/pⱼ must be defined; for sorted ratios the pairwise and adjacent tie rules are equivalent; vⱼ < 1 follows from vⱼ < pⱼ ≤ 1; no instance changes
--   - reading: qⱼ < 1 assumed "without loss of generality" (p.10) → qⱼ < 1 for every type, as a field of Instance; reason: the paper's standing assumption for all its results; the one-sentence reduction for qⱼ ≥ 1 is a remark, not a theorem, and is not formalized
--   - encoding: types 1,…,k and periods 1,…,T → Fin k and Fin T (0-based); 1-based period t of H_A⃗[t] kept as a natural-number argument; reason: Lean indexing; same objects
--   - reading: line 6 of Algorithm 1: "Find optimal index solution x⃗′" (which one unspecified) → any selection rule sel(t, past, Ñ) returning an optimal index solution locally optimal at its threshold index (IsAdmissibleRule), quantified after the constant; reason: p.21 states that this is the only property assumed of x⃗′; requiring it at every input rather than reachable ones changes no run (a rule admissible on reachable inputs extends to all inputs by exists_admissible)
--   - reading: line 7 of Algorithm 1: x′ⱼ ≥ Nᶠⱼ[t]/2 (prose on p.11: x_j̃ > Ñᶠⱼ[t]/2) → accept iff (x′ⱼ : ℝ) ≥ Ñᶠⱼ[t]/2; reason: the tilde is missing in line 7 (line 6 uses Ñ); the box's ≥ is the definition, as used in the proof of Lemma 3 (p.26)
--   - reading: "there exists a constant M₂" → ∃ M₂ chosen before B, T (and everything else); reason: footnote 3, p.12: constant means independent of B and T
--   - encoding: P over A⃗ → probability over the independent pair (A⃗, A⃗′) with weight Πλ(Aₜ)·Πλ(A′ₜ); reason: H_A⃗[t] depends on the policy's decisions, hence on A⃗′
-- source:
--   D. Freund and J. Zhao, Overbooking with bounded loss, arXiv:2204.11148v2 (26 Apr 2022), https://arxiv.org/abs/2204.11148v2, Lemma 3, p.14 (proof §4.3, pp.26–28)

import Definitions.Def_OverbookBL_expectedLoss

namespace OverbookBL

/-- **Lemma 3** (Freund & Zhao, *Overbooking with bounded loss*, arXiv:2204.11148v2, p.14). There
exists a constant `M₂` such that
`∑_{t=2}^{T} P[H_A⃗[t−1] − H_A⃗[t] > 0] ≤ M₂`,
for every capacity `B`, horizon `T` and admissible choice of the optimal index solution in line 6
of Algorithm 1.

**Formalization Note** `H_A⃗[t]` (`Hyb`) depends on the online policy's past decisions, hence on
the sample `A⃗′`; the probability is over the independent i.i.d. sequences `A⃗` and `A⃗′`, with
weight `∏ₜ λ_{Aₜ} ∏ₜ λ_{A′ₜ}`. `M₂` is chosen before `B`, `T` and the selection rule. Problem (1)
is read with `−V_B`. -/
theorem lemma_3 {k : ℕ} (I : Instance k) : ∃ M₂ : ℝ, ∀ (B T : ℕ) (sel : ℕ → (Fin k → ℕ) → (Fin k → ℕ) → (Fin k → ℕ)), IsAdmissibleRule I B sel → ∑ t ∈ Finset.Icc 2 T, ∑ A : Fin T → Fin k, ∑ A' : Fin T → Fin k, seqWeight I A * seqWeight I A' * (if 0 < Hyb I B sel A A' (t - 1) - Hyb I B sel A A' t then 1 else 0) ≤ M₂ := by sorry

end OverbookBL
