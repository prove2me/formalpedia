-- Prove2me | Theorems.Thm_StructBandit_lemma_11
-- name    : StructBandit.lemma_11
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T13:36:27.485863+00:00
-- url     : https://prove2.me/theorems/c23126a9-ae22-4b46-9338-5d0c60ad52a4
-- title:
--   Lemma 11 — in an exploration round, $N_t(x_t)\le(1+\epsilon)\|\eta_t\|_\infty\log T$
-- statement:
--   Let $\mathcal P$ be a structure set and $0<\epsilon<1/|X|$, and run DUSA. During an exploration round $t\le T$, with $\eta_t=\mathsf{SU}(P_t,\eta'_t;\mu_t,\epsilon)$ the target rate of that round,
--
--   $$
--   N_t(x_t)\le(1+\epsilon)\|\eta_t\|_\infty\log(T).
--   $$
--
--   It bounds the number of good exploration rounds in which an arm is played.
--
--   Differences from the source:
--
--   - generalization: stated under the hypotheses of Theorem 3, including P ∈ 𝒫′ (App. D) → no hypothesis on P; every history DUSA can produce, for any rewards; reason: the statement involves only DUSA's counters and targets; holding for all reward sequences it holds for those drawn from P ∈ 𝒫′
--   - encoding: ‖η_t‖∞ with η_t = +∞ when (19) is infeasible → the claim for η_t = some η, with ‖η‖∞ = max_x |η(x)|; reason: for η_t = +∞ the right side is +∞ and there is nothing to prove; the norm runs over all arms because x̄_t ranges over X in the box (p.24), whereas p.28 glosses ‖η′_ε(P)‖∞ over X̃(P)
--   - encoding: an event of the random run, any T ≥ t → a deterministic statement for every history DUSA can produce and every T ≥ t = |h| + 1; reason: the claim holds outcome by outcome
--   - reading: DUSA (Algorithm 1, p.24) leaves open the order of the initial pulls, the initial η′ and µ, which element of each argmin set is pulled, and the deep update's output when (20) has no minimizer → all of these are fields of an arbitrary DusaRules structure (functions of the seed and the history, constrained to the argmin sets; the fallback is nonnegative and dual-feasible), quantified universally; reason: the result must hold for every implementation of DUSA; every output of (20) and of the initialization is nonnegative and dual-feasible, and the sufficient-information test relies on dual feasibility (p.54)
--   - reading: the exploration bullets 'pull the least pulled arm' and 'pull x⋆_t / x̄_t' (p.24); x̄_t ∈ argmin over X (box) vs over X̃(P_t) (p.25); X⋆_t undefined in the box → the second pull is the alternative of the first; SU and DU are computed in every exploration round; x̄_t ∈ argmin over X; X⋆_t = x⋆(P_t); reason: the prose (p.25, 'Otherwise') and p.28 ('the number of updates is equal to the number of the exploration rounds'); the box is the algorithm
--   - encoding: P_t, N_t built by Algorithm 1's initialization and recursive update (p.24) → empirical distribution and pull counts of the history of the first t − 1 rounds; reason: the recursion produces exactly the empirical distribution after the point-mass initialization
--   - reading: (20) types µ(x) ∈ K⋆ × ℝ₊ × ℝ and writes λ(r,x)(x′) → α(x) ∈ ℝ₊, β(x) ∈ ℝ, λ(x) ∈ K⋆; λ(r,x)(x′) is the (r,x) entry of λ(x′), for every r ∈ R; reason: the order and roles of (α, β, λ) used everywhere else in the paper (pp.22, 24)
--   - reading: χ_{−∞}(η(x) − λ(r,x) − β − αr𝟙(x = x′) ≥ 0) in (14), with no index range → the constraint for every x ∈ X̃(P), r ∈ R; a log term is 0 if η(x)P(r,x) = 0 and −∞ if its argument is 0; reason: the range of the sum it closes, and the values the derivation of App. C.2 (p.43) gives at the boundary
--   - encoding: I, Dist, C, C̄, Rewmax, Dual, Dual‾ as extended-real optimal values ('max' over ρ ≥ 0 in (17) and 'max' in (8) included); SU := +∞ if (19) is infeasible → EReal values with inf ∅ = +∞, sup ∅ = −∞; SU returns Option (none = +∞), and none also when (19) is feasible but has no minimizer; reason: the source's conventions; a supremum need not be attained off the source's setting; (19) is an argmin, so nothing is defined without a minimizer; Lean's log 0 = 0 and x/0 = 0 decide no case
--   - encoding: N_t(x)/η_t(x) in argmin_x N_t(x)/η_t(x) (p.24), with η_t = +∞ possible → computed in ℝ≥0∞ with N/0 = +∞ for N ≥ 1 and N/(+∞) = 0; reason: the values the source intends; Lean's real x/0 = 0 would make an arm with zero target rate look most urgent
-- source:
--   Van Parys & Golrezaei, Optimal Learning for Structured Bandits, arXiv:2007.07302v3, Lemma 11, p.56 (proof App. G.2, p.72)

import Mathlib
import Definitions.Def_StructBandit_dusaPolicy

open scoped BigOperators

namespace StructBandit

/-- **Lemma 11.**
Van Parys & Golrezaei, arXiv:2007.07302v3, Lemma 11, p.56 (proof App. G.2, p.72).

During an exploration round `t ≤ T`, `N_t(x_t) ≤ (1+ε)‖η_t‖_∞ log(T)`, where `η_t = SU(P_t, η′_t; µ_t, ε)`
is the shallow-update target of round `t`.

**Formalization Note.** Under the standing hypotheses of Theorem 3 (`0 < ε < 1/|X|`). Deterministic, for
every history DUSA can produce and every `T ≥ t = |h| + 1`. When the shallow update returns `+∞` (`none`)
the right side is `+∞` and there is nothing to prove, so the statement is made for `η_t = some η`, with
`‖η‖_∞ = max_x |η(x)|`, the norm over all arms: `x̄_t` ranges over `X` in Algorithm 1, so the pulled arm
need not be suboptimal for `P_t`. -/
theorem lemma_11 {X : Type*} [Fintype X] [Nonempty X] {R : Finset ℝ} {S : Set (R → X → ℝ)}
    (hS : IsStructureSet S) {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1 / (Fintype.card X : ℝ))
    {V : Type*} (rules : DusaRules S V) (v : V) (h : History R X) (T : ℕ)
    (hh : IsDusaHistory S ε rules v h) (hX : IsExplorationAt S ε rules v h)
    (hT : h.length + 1 ≤ T) (η : X → ℝ) (hη : etaAt S ε rules v h = some η) :
    (pullCount h (dusaPolicy S ε rules v h) : ℝ)
      ≤ (1 + ε) * Finset.univ.sup' Finset.univ_nonempty (fun x => |η x|) * Real.log T := by sorry

end StructBandit
