-- Prove2me | Theorems.Thm_StationaryBwK_theorem_5_2
-- name    : StationaryBwK.theorem_5_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:52:28.597071+00:00
-- url     : https://prove2.me/theorems/89e34126-4785-40c2-aad2-1f9338c03e42
-- title:
--   Theorem 5.2: against an adaptive $(\sigma_r,\sigma_c)$-stationary adversary, $\mathrm{REW}\ge(\rho+\sigma_r(\sigma_c-\rho)^+)\mathrm{OPT}_{FD}-\mathrm{Err}(\delta)$ w.p. $\ge1-\delta$
-- statement:
--   Consider Bandits with Knapsacks with $T\ge1$ rounds, $d$ resources each with budget $B$, $0<B\le T$, $\rho=B/T$, and $K$ actions including a null action. The adversary is adaptive and $(\sigma_r,\sigma_c)$-stationary with $\sigma_r,\sigma_c\in[0,1]$: almost surely, for every action $a$ and resource $i$,
--   $$\min_{t\in[T]}r_t(a)\ge\sigma_r\max_{t\in[T]}r_t(a),\qquad\min_{t\in[T]}c_{t,i}(a)\ge\sigma_c\max_{t\in[T]}c_{t,i}(a),$$
--   where $r_t(a)$ and $c_{t,i}(a)$ are the expected reward and consumption conditioned on the history before round $t$. The player runs Algorithm 1: its maximizing and minimizing subroutines choose $A_t$ and $I_t$ without knowledge of round $t$ and satisfy the no-regret guarantees (4) and (5) with functions $\mathrm{Reg}_{\max}$, $\mathrm{Reg}_{\min}$. Then for any $\delta>0$, with probability at least $1-\delta$,
--   $$\mathrm{REW}\ \ge\ \big(\rho+\sigma_r(\sigma_c-\rho)^+\big)\,\mathrm{OPT}_{FD}-\mathrm{Err}(\delta),$$
--   where $\mathrm{OPT}_{FD}$ is the best fixed distribution of actions in hindsight (1) of the realized history and
--   $$\mathrm{Err}(\delta)=\mathrm{Reg}_{\max}(\delta/3)+\mathrm{Reg}_{\min}(\delta/3)+\Big(1+\frac1\rho\Big)\sqrt{2T\log(3TK/\delta)}+\frac1\rho .$$
--
--   This is Theorem 5.2 of the paper with its $O(\cdot)$-defined error terms $\mathrm{Reg}_{\max}(T,\delta)+\mathrm{Reg}_{\min}(T,\delta)$ replaced by the explicit error its proof yields; the competitive ratio $\rho+\sigma_r(\sigma_c-\rho)^+$ and the probability $1-\delta$ are exactly the paper's. The ratio interpolates between $\rho$ for a fully adversarial environment ($\sigma_r=\sigma_c=0$) and $1$ for a stochastic one ($\sigma_r=\sigma_c=1$), without the algorithm knowing $\sigma_r$ or $\sigma_c$.
--
--   **Formalization Note** The model (filtration, adaptedness, no-knowledge condition) is `IsBwKEnvironment` and `IsBwKPlayer`; the subroutines enter only through (4) and (5).
--
--   Differences from the source:
--   - reading: additive error Reg_max(T, δ) + Reg_min(T, δ), defined with O(·) in (4), (5) → Reg_max(δ/3) + Reg_min(δ/3) + (1 + 1/ρ)√(2T log(3TK/δ)) + 1/ρ; reason: this is the error the proof of Lemma 5.1 yields with δ₁ = δ₂ = δ₃ = δ/3 (p.16), which the paper absorbs into the O(·) definition of Reg_max; with abstract Reg functions the printed form has no room for the Azuma term and the 1/ρ of (9)
--   - generalization: Algorithm 1 with EXP3.P as Alg_max and Hedge as Alg_min → any adapted choices A_t, I_t satisfying (4) and (5) with arbitrary functions Regmax, Regmin of δ; reason: the proof (pp.15–18) uses the subroutines only through (4) and (5); EXP3.P and Hedge satisfy them by [Aue+02] and [FS97]
--   - generalization: the player chooses A_t (and I_t) without any knowledge of the reward or consumptions of that round or their distribution → conditional mean independence: E[R_t(a) | ℋ_{t−1} ∨ σ(A_t, I_t)] = E[R_t(a) | ℋ_{t−1}] a.s., and the same for C_{t,i}(a); reason: implied by conditional independence of round t's rewards and consumptions from the round-t choices; it is the only form the martingale step on p.16 uses
--   - reading: r_t(a) = E[R_t(a) | H_{t−1}] for the history H_t of actions and realized rewards and consumptions → a filtration ℋ to which R_t, C_t, A_t and I_t are adapted, with r_t(a) = E[R_t(a) | ℋ_{t−1}] and c_{t,i}(a) likewise; reason: the martingale Z on p.16 uses I_t, so Alg_min's choices must be in the history; the paper's H_t enlarged by the player's own choices is an instance
--   - reading: the game ends after round T or when a resource is depleted; T_A = max{t ∈ [T] : ∀i, Σ_{τ≤t} C_{τ,i}(A_τ) ≤ B} → R, C, A, I are defined on all rounds 1, …, T and only REW is cut at T_A; T_A = 0 when the set is empty; reason: OPT_FD and Definition 3.1 range over all t ∈ [T]; if round 1 already overdraws the player receives no reward
--   - encoding: Definition 3.1: for any action a, resource i and history H_T → almost surely, for every action and resource; reason: r and c are conditional expectations, defined up to null sets
--   - encoding: with probability at least 1 − δ → there is a measurable event E with μ(E) ≥ 1 − δ on which the inequality holds; reason: avoids the measure of a possibly non-measurable set; same meaning
--   - encoding: (4), (5) hold for all T′ → (4), (5) hold for all T′ ∈ {0, …, T}; reason: T′ = 0 gives empty sums and only forces Reg ≥ 0 (for δ < 1), which the paper's Reg_max, Reg_min are
--   - encoding: OPT_FD = max over T* ∈ [T], A* ∈ Δ([K]) in (1) → the supremum (sSup) of the feasible values, which is attained (optFD_attained); reason: Lean convention; equal to the maximum whenever it exists
--   - encoding: rounds t ∈ [T], actions [K] with a null action, resources [d], Alg_min's choice i ∈ [d] ∪ {0} → rounds are natural numbers 1, …, T; actions Fin K with a designated null action a₀; resources Fin d; i ∈ Option (Fin d) with none = 0; reason: Lean convention; same instances
-- source:
--   G. Fikioris and É. Tardos, Approximately Stationary Bandits with Knapsacks, arXiv:2302.14686v2 [cs.LG] (preprint, 8 Jul 2023), https://arxiv.org/abs/2302.14686v2, Theorem 5.2, p.10; proof pp.15–18 (Lemma 5.1, Lemmas A.1, A.2, proof of Theorem 5.2)

import Mathlib
import Definitions.Def_StationaryBwK_Benchmark
import Definitions.Def_StationaryBwK_StationarySeq
import Definitions.Def_StationaryBwK_Play
import Definitions.Def_StationaryBwK_Model
import Definitions.Def_StationaryBwK_Regret

open MeasureTheory

namespace StationaryBwK

/-- **Theorem 5.2** (Fikioris & Tardos, *Approximately Stationary Bandits with Knapsacks*,
arXiv:2302.14686v2, Theorem 5.2, p.10; proof pp.15–18). Against an adaptive `(σr, σc)`-stationary
adversary, the reward of Algorithm 1 satisfies, for any `δ > 0`, with probability at least `1 − δ`,
`REW ≥ (ρ + σr (σc − ρ)⁺) OPT_FD − Err(δ)`, where
`Err(δ) = Reg_max(T, δ/3) + Reg_min(T, δ/3) + (1 + 1/ρ)√(2T log(3TK/δ)) + 1/ρ`.

Setting: `T ≥ 1` rounds, `d` resources with budget `0 < B ≤ T` each, `ρ = B/T`, `K` actions
including a null action `a₀`, `σr, σc ∈ [0, 1]`; `R, C` the adversary's rewards and consumptions,
`A, I` the choices of `Alg_max` and `Alg_min`, whose guarantees (4) and (5) hold with the functions
`Regmax`, `Regmin`.

**Formalization Note.** The printed error `Reg_max(T, δ) + Reg_min(T, δ)` is defined only up to
`O(·)` in (4)–(5); `Err(δ)` (`lagrErr`) is the explicit error the proof yields. Algorithm 1's
subroutines enter only through (4) and (5). `OPT_FD` is the random variable `optFDRand`. -/
theorem theorem_5_2 {Ω : Type*} [m0 : MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℋ : Filtration ℕ m0) {d K : ℕ} (T : ℕ) (B : ℝ) (hT : 1 ≤ T) (hB : 0 < B) (hBT : B ≤ T)
    (a₀ : Fin K) (R : ℕ → Ω → Fin K → ℝ) (C : ℕ → Ω → Fin d → Fin K → ℝ)
    (A : ℕ → Ω → Fin K) (I : ℕ → Ω → Option (Fin d))
    (hEnv : IsBwKEnvironment ℋ T a₀ R C) (hPlayer : IsBwKPlayer μ ℋ T R C A I)
    (σr σc : ℝ) (hσr₀ : 0 ≤ σr) (hσr₁ : σr ≤ 1) (hσc₀ : 0 ≤ σc) (hσc₁ : σc ≤ 1)
    (hStat : IsStationaryAdversary μ ℋ T σr σc R C)
    (Regmax Regmin : ℝ → ℝ) (h4 : MaxRegretBound μ T B R C A I Regmax)
    (h5 : MinRegretBound μ T B R C A I Regmin) :
    ∀ δ : ℝ, 0 < δ → ∃ E : Set Ω, MeasurableSet E ∧ 1 - δ ≤ μ.real E ∧
      ∀ ω ∈ E,
        (rho T B + σr * max (σc - rho T B) 0) * optFDRand μ ℋ T B R C ω -
            lagrErr T K (rho T B) Regmax Regmin δ ≤ rew T B R C A ω := by sorry

end StationaryBwK
