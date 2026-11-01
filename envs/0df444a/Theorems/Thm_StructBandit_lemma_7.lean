-- Prove2me | Theorems.Thm_StructBandit_lemma_7
-- name    : StructBandit.lemma_7
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T13:36:04.161929+00:00
-- url     : https://prove2.me/theorems/782ac187-9c00-46ac-b716-2ccd32b2cf99
-- title:
--   Lemma 7 — finite regret of exploitation rounds with a badly estimated empirical optimum (corrected: bound times $\max(1,\max_x\Delta(x,P))$)
-- statement:
--   Let $\mathcal P$ be a structure set, $P\in\mathcal P'$ the true distribution and $0<\epsilon<1/|X|$, and run DUSA. With the bad event $\mathcal B^1_t(x,\kappa)=\{\|P_t(x)-P(x)\|_\infty>\kappa\}$, for every $\kappa>0$ and every $T$,
--
--   $$
--   \mathbb E\Big[\sum_{|X|<t\le T}\mathbb 1\Big\{\mathcal E_t,\ \bigcup_{x\in x^\star(P_t)}\mathcal B^1_t(x,\kappa)\Big\}\cdot\Delta(x_t,P)\Big]\le\Big(8|X|+|X||\mathfrak R|\sum_{1\le s\le T}2\exp\big(-s\kappa^2/(2|X|)\big)\Big)\cdot\max\Big(1,\max_{x}\Delta(x,P)\Big).
--   $$
--
--   The bound is uniform in $T$ up to a convergent series, so these rounds contribute $O(1)$ regret.
--
--   Differences from the source:
--
--   - correction: right side 8|X| + |X||R| Σ_{1≤s≤T} 2exp(−sκ²/(2|X|)) for any nonnegative rewards (the proof uses 'the regret in each round is bounded by one', pp.53, 68) → the right side multiplied by max(1, max_x ∆(x,P)), which is the printed bound whenever ∆ ≤ 1 (e.g. rewards in [0, 1]); reason: counterexample: R = {0, M}, two arms, 𝒫 = P_Ω, P(M,a) = 1/2, P(M,b) = 3/5 (P ∈ 𝒫′), κ = 1/10, T = 3: with probability 1/2·2/5 the initial pulls give a reward M and b reward 0; then X̃d(P_3) = ∅ (Rewmax(b,P_3) = M = Rew⋆(P_3)), round 3 exploits a with ‖P_3(a) − P(a)‖∞ = 1/2 > κ, so the left side is ≥ (1/5)(M/10) = M/50, while the printed right side is ≤ 40; it fails for M > 2000
--   - reading: Assumption 1(2): Rewmax(x,P) ≠ Rew⋆(P) for any x ∈ X (p.19) → Rewmax(x,P) ≠ Rew⋆(P) for every suboptimal x ∈ X̃(P) (PPrime); reason: as printed it fails at x = x⋆(P) for every P (Q = P is feasible in (8) and fixes the optimal column), so 𝒫′ would be empty and the statement vacuous; the paper's gloss (p.19) and counterexample (p.20) concern suboptimal arms
--   - reading: DUSA (Algorithm 1, p.24) leaves open the order of the initial pulls, the initial η′ and µ, which element of each argmin set is pulled, and the deep update's output when (20) has no minimizer → all of these are fields of an arbitrary DusaRules structure (functions of the seed and the history, constrained to the argmin sets; the fallback is nonnegative and dual-feasible), quantified universally; reason: the result must hold for every implementation of DUSA; every output of (20) and of the initialization is nonnegative and dual-feasible, and the sufficient-information test relies on dual feasibility (p.54)
--   - reading: the exploration bullets 'pull the least pulled arm' and 'pull x⋆_t / x̄_t' (p.24); x̄_t ∈ argmin over X (box) vs over X̃(P_t) (p.25); X⋆_t undefined in the box → the second pull is the alternative of the first; SU and DU are computed in every exploration round; x̄_t ∈ argmin over X; X⋆_t = x⋆(P_t); reason: the prose (p.25, 'Otherwise') and p.28 ('the number of updates is equal to the number of the exploration rounds'); the box is the algorithm
--   - reading: policies in Π: the arm of round t is F_t-measurable (p.7) → hypothesis IsMeasurableRun: DUSA's arm and exploration counter are measurable functions of the seed at every history; reason: this is what makes DUSA a member of Π and its expectations defined; it holds for any rule using finitely many seed values (e.g. a trivial seed)
--   - encoding: rewards R_t(x) independent across arms and rounds with law P(·,x) (p.7); expectation over rewards and DUSA's choices (p.28) → BanditEnv: an independent reward table indexed by ℕ × X with μ.real{R_t(x) = r} = P(r,x), and a seed independent of the table; reason: standard table representation of the model; the seed carries DUSA's randomized choices
--   - encoding: P_t, N_t built by Algorithm 1's initialization and recursive update (p.24) → empirical distribution and pull counts of the history of the first t − 1 rounds; reason: the recursion produces exactly the empirical distribution after the point-mass initialization
--   - encoding: I, Dist, C, C̄, Rewmax, Dual, Dual‾ as extended-real optimal values ('max' over ρ ≥ 0 in (17) and 'max' in (8) included); SU := +∞ if (19) is infeasible → EReal values with inf ∅ = +∞, sup ∅ = −∞; SU returns Option (none = +∞), and none also when (19) is feasible but has no minimizer; reason: the source's conventions; a supremum need not be attained off the source's setting; (19) is an argmin, so nothing is defined without a minimizer; Lean's log 0 = 0 and x/0 = 0 decide no case
--   - reading: (20) types µ(x) ∈ K⋆ × ℝ₊ × ℝ and writes λ(r,x)(x′) → α(x) ∈ ℝ₊, β(x) ∈ ℝ, λ(x) ∈ K⋆; λ(r,x)(x′) is the (r,x) entry of λ(x′), for every r ∈ R; reason: the order and roles of (α, β, λ) used everywhere else in the paper (pp.22, 24)
--   - reading: χ_{−∞}(η(x) − λ(r,x) − β − αr𝟙(x = x′) ≥ 0) in (14), with no index range → the constraint for every x ∈ X̃(P), r ∈ R; a log term is 0 if η(x)P(r,x) = 0 and −∞ if its argument is 0; reason: the range of the sum it closes, and the values the derivation of App. C.2 (p.43) gives at the boundary
--   - encoding: N_t(x)/η_t(x) in argmin_x N_t(x)/η_t(x) (p.24), with η_t = +∞ possible → computed in ℝ≥0∞ with N/0 = +∞ for N ≥ 1 and N/(+∞) = 0; reason: the values the source intends; Lean's real x/0 = 0 would make an arm with zero target rate look most urgent
-- source:
--   Van Parys & Golrezaei, Optimal Learning for Structured Bandits, arXiv:2007.07302v3, Lemma 7, Eq. (37), p.53 (proof App. F, p.68)

import Mathlib
import Definitions.Def_StructBandit_dusaPolicy

open scoped BigOperators
open MeasureTheory ProbabilityTheory

namespace StructBandit

open Classical in
/-- **Lemma 7 (Regret under the Bad Events in the Exploitation Phase).**
Van Parys & Golrezaei, arXiv:2007.07302v3, Lemma 7, Eq. (37), p.53 (proof App. F, p.68).

With the bad event `B¹_t(x,κ) = {‖P_t(x) − P(x)‖_∞ > κ}` (p.53),
`E[∑_{|X|<t≤T} 𝟙{E_t, ⋃_{x∈x⋆(P_t)} B¹_t(x,κ)} · ∆(x_t,P)] ≤ 8|X| + |X||R| ∑_{1≤s≤T} 2exp(−sκ²/(2|X|))`
for any `κ > 0`, under the standing hypotheses of Theorem 3 (`P ∈ 𝒫′`, `0 < ε < 1/|X|`, any run of DUSA).

**Formalization Note (correction).** The proof bounds `∆(x_t,P)` by one ("the regret in each round is
bounded by one", pp.53, 68), which holds when rewards lie in `[0,1]`; the model (p.7) allows any
nonnegative rewards, and then the printed bound is false: with `R = {0, M}`, two arms, `𝒫 = P_Ω`,
`P(M,a) = 1/2`, `P(M,b) = 3/5` (so `P ∈ 𝒫′`), `κ = 1/10`, `T = 3`, with probability `1/5` the initial pulls
give `a` the reward `M` and `b` the reward `0`; then no arm is empirically deceitful, round 3 exploits `a`
with `‖P_3(a) − P(a)‖_∞ = 1/2 > κ`, and the left side is at least `M/50`, while the printed right side is
at most `40`. The right side is therefore multiplied by `max(1, max_x ∆(x,P))`, which is `1`, the printed
bound, whenever `∆ ≤ 1`. Round `t = n + 1` sees the history of `n` rounds; `|X| < t ≤ T` is
`n ∈ [|X|, T)`. -/
theorem lemma_7 {X : Type*} [Fintype X] [Nonempty X] {R : Finset ℝ} {S : Set (R → X → ℝ)}
    (hS : IsStructureSet S) {P : R → X → ℝ} (hP : P ∈ PPrime S) {ε : ℝ} (hε0 : 0 < ε)
    (hε1 : ε < 1 / (Fintype.card X : ℝ))
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {V : Type*} [MeasurableSpace V] (E : BanditEnv P μ V) (rules : DusaRules S V)
    (hmeas : IsMeasurableRun S ε rules) (κ : ℝ) (hκ : 0 < κ) (T : ℕ) :
    ∫ ω, ∑ n ∈ Finset.Ico (Fintype.card X) T,
        (if IsExploitationAt S ε rules (E.seed ω) (histAt (dusaPolicy S ε rules) E n ω) ∧
            ∃ x ∈ optArms (empDist (histAt (dusaPolicy S ε rules) E n ω)), ∃ r : R,
              κ < |empDist (histAt (dusaPolicy S ε rules) E n ω) r x - P r x|
          then gap P (armAt (dusaPolicy S ε rules) E n ω) else 0) ∂μ
      ≤ (8 * (Fintype.card X : ℝ) + (Fintype.card X : ℝ) * (R.card : ℝ) *
            ∑ s ∈ Finset.Icc 1 T, 2 * Real.exp (-((s : ℝ) * κ ^ 2) / (2 * (Fintype.card X : ℝ))))
          * max 1 (Finset.univ.sup' Finset.univ_nonempty (gap P)) := by sorry

end StructBandit
