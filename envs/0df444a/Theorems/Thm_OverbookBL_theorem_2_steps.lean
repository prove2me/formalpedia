-- Prove2me | Theorems.Thm_OverbookBL_theorem_2_steps
-- name    : OverbookBL.theorem_2_steps
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:55:54.069704+00:00
-- url     : https://prove2.me/theorems/1f1946db-3953-4811-85c6-9976c8d0fae9
-- title:
--   Proof of Theorem 2 — $\mathcal H_{\vec A}[T]=\mathrm{OBJ}_{\vec A}$ and one period changes $\mathcal H$ by at most $1$ (corrected: $-V_B$ in (1))
-- statement:
--   For every capacity $B$, horizon $T\ge1$, admissible selection rule, arrival sequence $\vec A$ and sample $\vec A'$ of the online index policy:
--
--   1. the hybrid clairvoyant index objective in the last period equals the objective of the online index policy,
--   $$\mathcal H_{\vec A}[T]=\sum_jv_jx_j[T]-V_B(\vec x[T]);$$
--   2. for every $t\in\{2,\dots,T\}$, $\ \mathcal H_{\vec A}[t-1]-\mathcal H_{\vec A}[t]\le1$.
--
--   These are the two facts behind the compensated-coupling argument: the telescoping sum ends at the online objective, and each period costs at most one unit.
--
--   Differences from the source:
--   - correction: problem (1) printed with + V_B(x⃗[t−1] + x⃗) (p.10) → objective Σⱼ vⱼ(pastⱼ + xⱼ) − V_B(past + x); reason: sign typo: the objective on p.9, Definition 2 (p.12) and the proof of Theorem 1 (p.24) subtract the compensation; with + Lemma 1 is false (k = 1, p₁ = 1, v₁ = 1/2, B = 0, no past, Ñ₁ = 1: x₁ = 1 is optimal, but (ii) needs 1 ≤ 1/2)
--   - encoding: the model of §2 (p.9) with implicit vⱼ ≥ 0, pⱼ > 0 and the tie rule for adjacent types → the structure Instance with explicit 0 ≤ vⱼ, 0 < pⱼ, and the tie rule for every pair i < j; vⱼ < 1 not a separate field; reason: vⱼ is a revenue and qⱼ = vⱼ/pⱼ must be defined; for sorted ratios the pairwise and adjacent tie rules are equivalent; vⱼ < 1 follows from vⱼ < pⱼ ≤ 1; no instance changes
--   - reading: qⱼ < 1 assumed "without loss of generality" (p.10) → qⱼ < 1 for every type, as a field of Instance; reason: the paper's standing assumption for all its results; the one-sentence reduction for qⱼ ≥ 1 is a remark, not a theorem, and is not formalized
--   - encoding: types 1,…,k and periods 1,…,T → Fin k and Fin T (0-based); 1-based period t of H_A⃗[t] kept as a natural-number argument; reason: Lean indexing; same objects
--   - reading: line 6 of Algorithm 1: "Find optimal index solution x⃗′" (which one unspecified) → any selection rule sel(t, past, Ñ) returning an optimal index solution locally optimal at its threshold index (IsAdmissibleRule), quantified after the constant; reason: p.21 states that this is the only property assumed of x⃗′; requiring it at every input rather than reachable ones changes no run (a rule admissible on reachable inputs extends to all inputs by exists_admissible)
--   - reading: line 7 of Algorithm 1: x′ⱼ ≥ Nᶠⱼ[t]/2 (prose on p.11: x_j̃ > Ñᶠⱼ[t]/2) → accept iff (x′ⱼ : ℝ) ≥ Ñᶠⱼ[t]/2; reason: the tilde is missing in line 7 (line 6 uses Ñ); the box's ≥ is the definition, as used in the proof of Lemma 3 (p.26)
--   - encoding: H_A⃗[T] = OBJ_A⃗ → Hyb T = onlineObj for each sample A⃗′; reason: H_A⃗[T] depends on A⃗′ and OBJ_A⃗ is the average over A⃗′; the pathwise equality is what the telescoping sum uses
-- source:
--   D. Freund and J. Zhao, Overbooking with bounded loss, arXiv:2204.11148v2 (26 Apr 2022), https://arxiv.org/abs/2204.11148v2, Proof of Theorem 2, p.14, "the last term is H_A[T] = OBJ_A" and "The starred inequality holds because"

import Definitions.Def_OverbookBL_expectedLoss

namespace OverbookBL

/-- **The two steps of the proof of Theorem 2** (Freund & Zhao, *Overbooking with bounded loss*,
arXiv:2204.11148v2, Proof of Theorem 2, p.14: "the last term is `H_A⃗[T] = OBJ_A⃗`" and "The
starred inequality holds because any action in one period affects the objective, through lost
revenue or incurred compensation, by at most 1"). For every capacity `B`, horizon `T ≥ 1`,
admissible selection rule, arrival sequence `A⃗` and sample `A⃗′`:
(a) the hybrid clairvoyant index objective in the last period equals the objective of the online
index policy, `H_A⃗[T] = ∑ⱼ vⱼ xⱼ[T] − V_B(x⃗[T])`;
(b) `H_A⃗[t−1] − H_A⃗[t] ≤ 1` for every `t ∈ {2, …, T}`.

**Formalization Note** The paper's `H_A⃗[T] = OBJ_A⃗` is stated pathwise, for each sample `A⃗′`
(`OBJ_A⃗` is its average over `A⃗′`). Periods `t` are 1-based as in the paper. Problem (1) is read
with `−V_B`. -/
theorem theorem_2_steps {k : ℕ} (I : Instance k) (B T : ℕ) (hT : 1 ≤ T) (sel : ℕ → (Fin k → ℕ) → (Fin k → ℕ) → (Fin k → ℕ)) (hsel : IsAdmissibleRule I B sel) (A A' : Fin T → Fin k) : Hyb I B sel A A' T = onlineObj I B sel A A' ∧ ∀ t ∈ Finset.Icc 2 T, Hyb I B sel A A' (t - 1) - Hyb I B sel A A' t ≤ 1 := by sorry

end OverbookBL
