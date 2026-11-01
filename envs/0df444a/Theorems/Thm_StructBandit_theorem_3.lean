-- Prove2me | Theorems.Thm_StructBandit_theorem_3
-- name    : StructBandit.theorem_3
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T13:36:27.341221+00:00
-- url     : https://prove2.me/theorems/527506e4-bedb-44f8-a9df-fb97da33197e
-- title:
--   Theorem 3 — DUSA: $\limsup\mathrm{Reg}/\log T\le(1+\epsilon)(C(P)+\epsilon(1+\sum_x\Delta))$, $\limsup\mathbb E[s_T]/\log T\le(1+\epsilon)|X|^2(\|\eta'_\epsilon(P)\|_\infty+\epsilon)$
-- statement:
--   Let $\mathcal P\subseteq\mathcal P_\Omega$ be a closed convex structure set with non-empty interior, let the true reward distribution be $P\in\mathcal P'$ (Assumption 1), and let $0<\epsilon<1/|X|$. Then every run of DUSA satisfies
--
--   $$
--   \limsup_{T\to\infty}\frac{\mathrm{Reg}_\pi(T,P)}{\log T}\le(1+\epsilon)\Big(C(P)+\epsilon\Big(1+\sum_{x\in X}\Delta(x,P)\Big)\Big),\qquad(21)
--   $$
--
--   where the regret is computed against the benchmark that knows the best arm in advance, and the expected number $s_T$ of exploration rounds before round $T$ satisfies
--
--   $$
--   \limsup_{T\to\infty}\frac{\mathbb E[s_T]}{\log T}\le(1+\epsilon)|X|^2\big(\|\eta'_\epsilon(P)\|_\infty+\epsilon\big),\qquad(22)
--   $$
--
--   where $\eta'_\epsilon(P)$ is the deep-update rate at $P$, $\|\eta'_\epsilon(P)\|_\infty=\max_{x\in\tilde X(P)}\eta'_\epsilon(x,P)$, and the expectation is over the rewards and DUSA's choices.
--
--   Since every uniformly good policy has $\liminf\mathrm{Reg}/\log T\ge C(P)$, (21) shows that DUSA's asymptotic regret matches the lower bound as $\epsilon\to0$, while (22) shows that its expensive updates run only $O(\log T)$ times.
--
--   Differences from the source:
--
--   - reading: Assumption 1(2): Rewmax(x,P) ≠ Rew⋆(P) for any x ∈ X (p.19) → Rewmax(x,P) ≠ Rew⋆(P) for every suboptimal x ∈ X̃(P) (PPrime); reason: as printed it fails at x = x⋆(P) for every P (Q = P is feasible in (8) and fixes the optimal column), so 𝒫′ would be empty and the statement vacuous; the paper's gloss (p.19) and counterexample (p.20) concern suboptimal arms
--   - reading: DUSA (Algorithm 1, p.24) leaves open the order of the initial pulls, the initial η′ and µ, which element of each argmin set is pulled, and the deep update's output when (20) has no minimizer → all of these are fields of an arbitrary DusaRules structure (functions of the seed and the history, constrained to the argmin sets; the fallback is nonnegative and dual-feasible), quantified universally; reason: the result must hold for every implementation of DUSA; every output of (20) and of the initialization is nonnegative and dual-feasible, and the sufficient-information test relies on dual feasibility (p.54)
--   - reading: the exploration bullets 'pull the least pulled arm' and 'pull x⋆_t / x̄_t' (p.24); x̄_t ∈ argmin over X (box) vs over X̃(P_t) (p.25); X⋆_t undefined in the box → the second pull is the alternative of the first; SU and DU are computed in every exploration round; x̄_t ∈ argmin over X; X⋆_t = x⋆(P_t); reason: the prose (p.25, 'Otherwise') and p.28 ('the number of updates is equal to the number of the exploration rounds'); the box is the algorithm
--   - reading: policies in Π: the arm of round t is F_t-measurable (p.7) → hypothesis IsMeasurableRun: DUSA's arm and exploration counter are measurable functions of the seed at every history; reason: this is what makes DUSA a member of Π and its expectations defined; it holds for any rule using finitely many seed values (e.g. a trivial seed)
--   - reading: η′_ε(P) in (22), presupposed → a conjunct asserting that the deep-update pair at P exists, and (22) for that pair; reason: (22) is meaningful only if η′_ε(P) exists (Proposition 4); asserting it keeps (22) from being vacuous
--   - encoding: limsup_{T→∞} a_T/log(T) ≤ b → for every real c > b, eventually a_T ≤ c·log T; reason: equivalent since log T > 0 eventually; b may be +∞ (C(P) is an extended real)
--   - encoding: s_T, the number of exploration rounds → DUSA's counter at the start of round T (after the history of T − 1 rounds); reason: Algorithm 1's s_T (s_{t+1} = s_t + 1 in exploration rounds)
--   - encoding: rewards R_t(x) independent across arms and rounds with law P(·,x) (p.7); expectation over rewards and DUSA's choices (p.28) → BanditEnv: an independent reward table indexed by ℕ × X with μ.real{R_t(x) = r} = P(r,x), and a seed independent of the table; reason: standard table representation of the model; the seed carries DUSA's randomized choices
--   - encoding: P_t, N_t built by Algorithm 1's initialization and recursive update (p.24) → empirical distribution and pull counts of the history of the first t − 1 rounds; reason: the recursion produces exactly the empirical distribution after the point-mass initialization
--   - encoding: I, Dist, C, C̄, Rewmax, Dual, Dual‾ as extended-real optimal values ('max' over ρ ≥ 0 in (17) and 'max' in (8) included); SU := +∞ if (19) is infeasible → EReal values with inf ∅ = +∞, sup ∅ = −∞; SU returns Option (none = +∞), and none also when (19) is feasible but has no minimizer; reason: the source's conventions; a supremum need not be attained off the source's setting; (19) is an argmin, so nothing is defined without a minimizer; Lean's log 0 = 0 and x/0 = 0 decide no case
--   - reading: (20) types µ(x) ∈ K⋆ × ℝ₊ × ℝ and writes λ(r,x)(x′) → α(x) ∈ ℝ₊, β(x) ∈ ℝ, λ(x) ∈ K⋆; λ(r,x)(x′) is the (r,x) entry of λ(x′), for every r ∈ R; reason: the order and roles of (α, β, λ) used everywhere else in the paper (pp.22, 24)
--   - reading: χ_{−∞}(η(x) − λ(r,x) − β − αr𝟙(x = x′) ≥ 0) in (14), with no index range → the constraint for every x ∈ X̃(P), r ∈ R; a log term is 0 if η(x)P(r,x) = 0 and −∞ if its argument is 0; reason: the range of the sum it closes, and the values the derivation of App. C.2 (p.43) gives at the boundary
--   - encoding: N_t(x)/η_t(x) in argmin_x N_t(x)/η_t(x) (p.24), with η_t = +∞ possible → computed in ℝ≥0∞ with N/0 = +∞ for N ≥ 1 and N/(+∞) = 0; reason: the values the source intends; Lean's real x/0 = 0 would make an arm with zero target rate look most urgent
-- source:
--   Van Parys & Golrezaei, Optimal Learning for Structured Bandits, arXiv:2007.07302v3, Theorem 3, Eqs. (21), (22), p.28 (proof App. D, pp.52–58)

import Mathlib
import Definitions.Def_StructBandit_dusaPolicy

open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter

namespace StructBandit

/-- **Theorem 3 (Regret Bound of DUSA).**
Van Parys & Golrezaei, *Optimal Learning for Structured Bandits*, arXiv:2007.07302v3, Theorem 3, p.28,
Eqs. (21), (22).

Let `S` (the paper's `𝒫`) be a closed convex structure set with non-empty interior, `P ∈ 𝒫′`
(Assumption 1) the true reward distribution and `0 < ε < 1/|X|`. For every run of DUSA (every choice of
the free choices of Algorithm 1, on any environment with an independent reward table of law `P` and an
independent randomization seed):
* (21) `limsup_{T→∞} Reg_π(T,P)/log(T) ≤ (1+ε)(C(P) + ε(1 + ∑_{x∈X} ∆(x,P)))`;
* (22) `limsup_{T→∞} E[s_T]/log(T) ≤ (1+ε)|X|²(‖η′_ε(P)‖_∞ + ε)`, where `η′_ε(P)` is the deep-update
  rate at `P` (it exists, Proposition 4) and `‖η′_ε(P)‖_∞ = max_{x∈X̃(P)} η′_ε(x,P)` (p.28).

**Formalization Note.** `limsup_T a_T/log T ≤ b` is stated as "for every real `c > b`, eventually
`a_T ≤ c log T`" (equivalent since `log T > 0` eventually; `b = C(P) + …` is an extended real, `+∞`
when (6) is infeasible). `s_T` is DUSA's exploration counter at the start of round `T`, i.e. after the
history of `T − 1` rounds. `IsMeasurableRun` makes DUSA's choices `F_t`-measurable (the class `Π`, p.7),
which every rule using finitely many seed values satisfies. -/
theorem theorem_3 {X : Type*} [Fintype X] [Nonempty X] {R : Finset ℝ} {S : Set (R → X → ℝ)}
    (hS : IsStructureSet S) {P : R → X → ℝ} (hP : P ∈ PPrime S) {ε : ℝ} (hε0 : 0 < ε)
    (hε1 : ε < 1 / (Fintype.card X : ℝ))
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {V : Type*} [MeasurableSpace V] (E : BanditEnv P μ V) (rules : DusaRules S V)
    (hmeas : IsMeasurableRun S ε rules) :
    (∀ c : ℝ, ((1 + ε : ℝ) : EReal) *
          (lowerBound S P + ((ε * (1 + ∑ x, gap P x) : ℝ) : EReal)) < (c : EReal) →
        ∀ᶠ T : ℕ in atTop, regret (dusaPolicy S ε rules) E T ≤ c * Real.log T) ∧
    (∃ η μs, IsDUSol S P ε η μs) ∧
    (∀ η μs, IsDUSol S P ε η μs → ∀ c : ℝ,
        (1 + ε) * (Fintype.card X : ℝ) ^ 2 * (maxOnSub P η + ε) < c →
        ∀ᶠ T : ℕ in atTop,
          ∫ ω, ((dusaState S ε rules (E.seed ω)
              (histAt (dusaPolicy S ε rules) E (T - 1) ω)).s : ℝ) ∂μ ≤ c * Real.log T) := by sorry

end StructBandit
