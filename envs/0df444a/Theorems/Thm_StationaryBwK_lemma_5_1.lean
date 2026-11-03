-- Prove2me | Theorems.Thm_StationaryBwK_lemma_5_1
-- name    : StationaryBwK.lemma_5_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:52:09.599305+00:00
-- url     : https://prove2.me/theorems/2091f2fe-e275-4b13-b767-a36f9b61bc35
-- title:
--   Lemma 5.1: $\mathrm{REW}\ge\sum_{t=1}^T\mathbb E_{a\sim A}[r_t(a)]-\mathrm{Err}(\delta)$ for every budget-feasible $A$
-- statement:
--   Consider the adaptive BwK model with $T\ge1$ rounds, $d$ resources, $K$ actions including a null action, budget $0<B\le T$ and $\rho=B/T$, against **any** adaptive adversary. Let the player's choices satisfy the no-knowledge condition and the no-regret guarantees (4) and (5) with functions $\mathrm{Reg}_{\max}$, $\mathrm{Reg}_{\min}$. Then for every $\delta>0$, with probability at least $1-\delta$, for every distribution of actions $A\in\Delta([K])$ with $\max_{i,t}\mathbb E_{a\sim A}[c_{t,i}(a)]\le\rho$,
--   $$\mathrm{REW}\ \ge\ \sum_{t=1}^{T}\mathbb E_{a\sim A}[r_t(a)]-\mathrm{Err}(\delta),\qquad \mathrm{Err}(\delta)=\mathrm{Reg}_{\max}(\delta/3)+\mathrm{Reg}_{\min}(\delta/3)+\Big(1+\frac1\rho\Big)\sqrt{2T\log(3TK/\delta)}+\frac1\rho .$$
--
--   This is (6) of the paper with the error its proof yields. It compares Algorithm 1 with any fixed distribution of actions that never exceeds the per-round budget in expectation, and it is the engine of Theorem 5.2.
--
--   Differences from the source:
--   - reading: additive error Reg_max(T, δ) + Reg_min(T, δ), defined with O(·) in (4), (5) → Reg_max(δ/3) + Reg_min(δ/3) + (1 + 1/ρ)√(2T log(3TK/δ)) + 1/ρ; reason: this is the error the proof of Lemma 5.1 yields with δ₁ = δ₂ = δ₃ = δ/3 (p.16), which the paper absorbs into the O(·) definition of Reg_max; with abstract Reg functions the printed form has no room for the Azuma term and the 1/ρ of (9)
--   - generalization: Algorithm 1 with EXP3.P as Alg_max and Hedge as Alg_min → any adapted choices A_t, I_t satisfying (4) and (5) with arbitrary functions Regmax, Regmin of δ; reason: the proof (pp.15–18) uses the subroutines only through (4) and (5); EXP3.P and Hedge satisfy them by [Aue+02] and [FS97]
--   - generalization: A fixed before 'with probability at least 1 − δ' → one event for all A ∈ Δ([K]) with max_{i,t} E_{a∼A}[c_{t,i}(a)] ≤ ρ at that outcome; reason: the proof's three events ((7), (8) and the Azuma event over all a) do not depend on A; this form specializes to the printed one and is the one the proof of Theorem 5.2 needs, where A depends on the history
--   - generalization: the player chooses A_t (and I_t) without any knowledge of the reward or consumptions of that round or their distribution → conditional mean independence: E[R_t(a) | ℋ_{t−1} ∨ σ(A_t, I_t)] = E[R_t(a) | ℋ_{t−1}] a.s., and the same for C_{t,i}(a); reason: implied by conditional independence of round t's rewards and consumptions from the round-t choices; it is the only form the martingale step on p.16 uses
--   - reading: r_t(a) = E[R_t(a) | H_{t−1}] for the history H_t of actions and realized rewards and consumptions → a filtration ℋ to which R_t, C_t, A_t and I_t are adapted, with r_t(a) = E[R_t(a) | ℋ_{t−1}] and c_{t,i}(a) likewise; reason: the martingale Z on p.16 uses I_t, so Alg_min's choices must be in the history; the paper's H_t enlarged by the player's own choices is an instance
--   - reading: the game ends after round T or when a resource is depleted; T_A = max{t ∈ [T] : ∀i, Σ_{τ≤t} C_{τ,i}(A_τ) ≤ B} → R, C, A, I are defined on all rounds 1, …, T and only REW is cut at T_A; T_A = 0 when the set is empty; reason: OPT_FD and Definition 3.1 range over all t ∈ [T]; if round 1 already overdraws the player receives no reward
--   - encoding: with probability at least 1 − δ → there is a measurable event E with μ(E) ≥ 1 − δ on which the inequality holds; reason: avoids the measure of a possibly non-measurable set; same meaning
--   - encoding: (4), (5) hold for all T′ → (4), (5) hold for all T′ ∈ {0, …, T}; reason: T′ = 0 gives empty sums and only forces Reg ≥ 0 (for δ < 1), which the paper's Reg_max, Reg_min are
--   - encoding: max_{i,t} E_{a∼A}[c_{i,t}(a)] ≤ ρ → E_{a∼A}[c_{t,i}(a)] ≤ ρ for every t ∈ [T] and i ∈ [d]; reason: the printed index order c_{i,t} is the paper's c_{t,i}; a maximum bound is a bound for every index
--   - encoding: rounds t ∈ [T], actions [K] with a null action, resources [d], Alg_min's choice i ∈ [d] ∪ {0} → rounds are natural numbers 1, …, T; actions Fin K with a designated null action a₀; resources Fin d; i ∈ Option (Fin d) with none = 0; reason: Lean convention; same instances
-- source:
--   G. Fikioris and É. Tardos, Approximately Stationary Bandits with Knapsacks, arXiv:2302.14686v2 [cs.LG] (preprint, 8 Jul 2023), https://arxiv.org/abs/2302.14686v2, Lemma 5.1, display (6), p.9; proof pp.15–16

import Mathlib
import Definitions.Def_StationaryBwK_Benchmark
import Definitions.Def_StationaryBwK_Play
import Definitions.Def_StationaryBwK_Model
import Definitions.Def_StationaryBwK_Regret

open MeasureTheory

namespace StationaryBwK

/-- **Lemma 5.1** (Fikioris & Tardos, arXiv:2302.14686v2, Lemma 5.1, (6), p.9; proof pp.15–16).
Against any adaptive adversary (no stationarity is assumed), let the player run Algorithm 1 with
subroutines satisfying (4) and (5). Then for every `δ > 0`, with probability at least `1 − δ`, for
**every** distribution of actions `A ∈ Δ([K])` with `max_{i,t} E_{a∼A}[c_{t,i}(a)] ≤ ρ`,
`REW ≥ Σ_{t=1}^{T} E_{a∼A}[r_t(a)] − Err(δ)`, where
`Err(δ) = Reg_max(T, δ/3) + Reg_min(T, δ/3) + (1 + 1/ρ)√(2T log(3TK/δ)) + 1/ρ` (`lagrErr`).

**Formalization Note.** The event does not depend on `A` (the proof's three events do not), so the
statement quantifies over `A` inside the event; the proof of Theorem 5.2 applies it to an `A` that
depends on the realized history. The printed error `Reg_max(T, δ) + Reg_min(T, δ)` is defined only up
to `O(·)`; `Err(δ)` is the error the proof on pp.15–16 yields with `δ₁ = δ₂ = δ₃ = δ/3`. -/
theorem lemma_5_1 {Ω : Type*} [m0 : MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℋ : Filtration ℕ m0) {d K : ℕ} (T : ℕ) (B : ℝ) (hT : 1 ≤ T) (hB : 0 < B) (hBT : B ≤ T)
    (a₀ : Fin K) (R : ℕ → Ω → Fin K → ℝ) (C : ℕ → Ω → Fin d → Fin K → ℝ)
    (A : ℕ → Ω → Fin K) (I : ℕ → Ω → Option (Fin d))
    (hEnv : IsBwKEnvironment ℋ T a₀ R C) (hPlayer : IsBwKPlayer μ ℋ T R C A I)
    (Regmax Regmin : ℝ → ℝ) (h4 : MaxRegretBound μ T B R C A I Regmax)
    (h5 : MinRegretBound μ T B R C A I Regmin) :
    ∀ δ : ℝ, 0 < δ → ∃ E : Set Ω, MeasurableSet E ∧ 1 - δ ≤ μ.real E ∧
      ∀ ω ∈ E, ∀ p ∈ stdSimplex ℝ (Fin K),
        (∀ t ∈ Finset.Icc 1 T, ∀ i : Fin d,
          expect p (fun a => cCond μ ℋ C t i a ω) ≤ rho T B) →
        ∑ t ∈ Finset.Icc 1 T, expect p (fun a => rCond μ ℋ R t a ω) -
            lagrErr T K (rho T B) Regmax Regmin δ ≤ rew T B R C A ω := by sorry

end StationaryBwK
