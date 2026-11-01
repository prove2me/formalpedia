-- Prove2me | Theorems.Thm_StructBandit_lemma_8
-- name    : StructBandit.lemma_8
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T13:36:28.312151+00:00
-- url     : https://prove2.me/theorems/7eec01f9-a14f-4941-86da-d5e68c0e321d
-- title:
--   Lemma 8 — an exploitation round that misses $x^\star(P)$ with accurate optimum estimates forces (39)
-- statement:
--   Let $\mathcal P$ be a structure set, $P\in\mathcal P'$ and $0<\epsilon<1/|X|$. There is $\kappa_0>0$ such that for every $\kappa\in(0,\kappa_0]$, every run of DUSA and every round $t>|X|$: if round $t$ is an exploitation round, $x^\star(P)\notin x^\star(P_t)$, and the bad event $\bigcup_{x\in x^\star(P_t)}\mathcal B^1_t(x,\kappa)$ does not occur (that is, $\|P_t(x)-P(x)\|_\infty\le\kappa$ for every $x\in x^\star(P_t)$), then
--
--   $$
--   \sum_{x\in X}N_t(x)\,I(P_t(x),P(x))\ge(1+\epsilon)\log(t).\qquad(39)
--   $$
--
--   Combined with Lemma 6, this bounds the regret of exploitation rounds that miss the optimal arm.
--
--   Differences from the source:
--
--   - reading: 'if the bad event … does not occur, then the event (39) must occur', in the setting of the display before it (pp.53–54) → hypotheses: round t > |X| is an exploitation round, x⋆(P) ∉ x⋆(P_t), and ‖P_t(x) − P(x)‖∞ ≤ κ for x ∈ x⋆(P_t); reason: the lemma bounds exactly the probability Prob[E_t, x⋆(P) ∉ x⋆(P_t), ‖P_t(x) − P(x)‖∞ ≤ κ ∀x ∈ x⋆(P_t)] of p.54
--   - reading: 'for small enough κ > 0' → ∃ κ₀ > 0 uniform over runs, seeds and rounds, ∀ κ ∈ (0, κ₀]; reason: the proof of Theorem 3 fixes κ once for all rounds
--   - encoding: an event of the random run → a deterministic statement for every history DUSA can produce (IsDusaHistory); reason: the claim holds outcome by outcome
--   - reading: Assumption 1(2): Rewmax(x,P) ≠ Rew⋆(P) for any x ∈ X (p.19) → Rewmax(x,P) ≠ Rew⋆(P) for every suboptimal x ∈ X̃(P) (PPrime); reason: as printed it fails at x = x⋆(P) for every P (Q = P is feasible in (8) and fixes the optimal column), so 𝒫′ would be empty and the statement vacuous; the paper's gloss (p.19) and counterexample (p.20) concern suboptimal arms
--   - reading: DUSA (Algorithm 1, p.24) leaves open the order of the initial pulls, the initial η′ and µ, which element of each argmin set is pulled, and the deep update's output when (20) has no minimizer → all of these are fields of an arbitrary DusaRules structure (functions of the seed and the history, constrained to the argmin sets; the fallback is nonnegative and dual-feasible), quantified universally; reason: the result must hold for every implementation of DUSA; every output of (20) and of the initialization is nonnegative and dual-feasible, and the sufficient-information test relies on dual feasibility (p.54)
--   - reading: the exploration bullets 'pull the least pulled arm' and 'pull x⋆_t / x̄_t' (p.24); x̄_t ∈ argmin over X (box) vs over X̃(P_t) (p.25); X⋆_t undefined in the box → the second pull is the alternative of the first; SU and DU are computed in every exploration round; x̄_t ∈ argmin over X; X⋆_t = x⋆(P_t); reason: the prose (p.25, 'Otherwise') and p.28 ('the number of updates is equal to the number of the exploration rounds'); the box is the algorithm
--   - encoding: P_t, N_t built by Algorithm 1's initialization and recursive update (p.24) → empirical distribution and pull counts of the history of the first t − 1 rounds; reason: the recursion produces exactly the empirical distribution after the point-mass initialization
--   - encoding: I, Dist, C, C̄, Rewmax, Dual, Dual‾ as extended-real optimal values ('max' over ρ ≥ 0 in (17) and 'max' in (8) included); SU := +∞ if (19) is infeasible → EReal values with inf ∅ = +∞, sup ∅ = −∞; SU returns Option (none = +∞), and none also when (19) is feasible but has no minimizer; reason: the source's conventions; a supremum need not be attained off the source's setting; (19) is an argmin, so nothing is defined without a minimizer; Lean's log 0 = 0 and x/0 = 0 decide no case
--   - reading: (20) types µ(x) ∈ K⋆ × ℝ₊ × ℝ and writes λ(r,x)(x′) → α(x) ∈ ℝ₊, β(x) ∈ ℝ, λ(x) ∈ K⋆; λ(r,x)(x′) is the (r,x) entry of λ(x′), for every r ∈ R; reason: the order and roles of (α, β, λ) used everywhere else in the paper (pp.22, 24)
--   - reading: χ_{−∞}(η(x) − λ(r,x) − β − αr𝟙(x = x′) ≥ 0) in (14), with no index range → the constraint for every x ∈ X̃(P), r ∈ R; a log term is 0 if η(x)P(r,x) = 0 and −∞ if its argument is 0; reason: the range of the sum it closes, and the values the derivation of App. C.2 (p.43) gives at the boundary
--   - encoding: N_t(x)/η_t(x) in argmin_x N_t(x)/η_t(x) (p.24), with η_t = +∞ possible → computed in ℝ≥0∞ with N/0 = +∞ for N ≥ 1 and N/(+∞) = 0; reason: the values the source intends; Lean's real x/0 = 0 would make an arm with zero target rate look most urgent
-- source:
--   Van Parys & Golrezaei, Optimal Learning for Structured Bandits, arXiv:2007.07302v3, Lemma 8, Eq. (39), p.54 (proof App. F, pp.69–70)

import Mathlib
import Definitions.Def_StructBandit_dusaPolicy

open scoped BigOperators

namespace StructBandit

/-- **Lemma 8.**
Van Parys & Golrezaei, arXiv:2007.07302v3, Lemma 8, Eq. (39), p.54 (proof App. F, pp.69–70).

"For small enough `κ > 0`, if the bad event `⋃_{x∈x⋆(P_t)} B¹_t(x,κ)` does not occur, then the event
defined in Equation (39) must occur", in the setting of the display before it (pp.53–54): round
`t > |X|` is an exploitation round (`E_t`) and `x⋆(P) ∉ x⋆(P_t)`. Event (39) is
`∑_{x∈X} N_t(x) I(P_t(x),P(x)) ≥ (1+ε) log(t)`.

**Formalization Note.** Under the standing hypotheses of Theorem 3 (`P ∈ 𝒫′`, `0 < ε < 1/|X|`). The
threshold `κ₀` is uniform: it does not depend on the run (rules, seed) nor on the round. The claim is
deterministic and is stated for every history DUSA can produce; round `t = |h| + 1`, `N_t` and `P_t` are
counted on `h`, and `‖P_t(x) − P(x)‖_∞ ≤ κ` is `|P_t(r,x) − P(r,x)| ≤ κ` for every `r`. -/
theorem lemma_8 {X : Type*} [Fintype X] [Nonempty X] {R : Finset ℝ} {S : Set (R → X → ℝ)}
    (hS : IsStructureSet S) {P : R → X → ℝ} (hP : P ∈ PPrime S) {ε : ℝ} (hε0 : 0 < ε)
    (hε1 : ε < 1 / (Fintype.card X : ℝ)) :
    ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
      ∀ {V : Type*} (rules : DusaRules S V) (v : V) (h : History R X),
        IsDusaHistory S ε rules v h → IsExploitationAt S ε rules v h →
        (∀ x₀ ∈ optArms P, x₀ ∉ optArms (empDist h)) →
        (∀ x ∈ optArms (empDist h), ∀ r : R, |empDist h r x - P r x| ≤ κ) →
        (((1 + ε) * Real.log ((h.length : ℝ) + 1) : ℝ) : EReal) ≤
          ∑ x, ((pullCount h x : ℝ) : EReal) * infoDist (fun r => empDist h r x) (fun r => P r x) := by sorry


end StructBandit
