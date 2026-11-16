-- Prove2me | Theorems.Thm_RobustCtxPricing_Supplement_theorem_6_1
-- name    : RobustCtxPricing.Supplement.theorem_6_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T02:06:08.636549+00:00
-- url     : https://prove2.me/theorems/855116b0-117e-4ef4-b9ae-b06c8888a8ce
-- title:
--   Theorem 6.1 — without knowing $C$, no algorithm gets $O(C)+o(\log^2T)$ regret with probability $1-1/T$, even for $d=1$
-- statement:
--   Let $\pi$ be any randomized online pricing learner for dimension $d=1$ that is not given the corruption budget $C$: its internal randomness lives on a probability space $\Omega$, and the price of round $t$ is a function of the horizon $T$, of $\omega$ (measurably), of the contexts $u_1,\dots,u_t$ and of the feedback $Y_1,\dots,Y_{t-1}$. Let $a\ge0$ be a constant and $g:\mathbb N\to\mathbb R$ any function with
--   $$
--   g(T)=o(\log^2T)\qquad(T\to\infty).
--   $$
--   Then for all sufficiently large $T$ the learner does **not** guarantee
--   $$
--   \mathbb P\big(R_T\le aC+g(T)\big)\ge1-\frac1T
--   $$
--   for every budget $C$ and every instance with $d=1$ ($\theta^\star\in[-1,1]$, contexts $u_t\in[-1,1]$ with $v_t\ge0$) whose at most $C$ attacked rounds are fixed in advance, with feedback a fixed measurable function of the posted price on the attacked rounds and the true sale bit elsewhere. In particular no such learner achieves $R_T=O(C)+o(\log^2T)$ with probability $1-1/T$ for all large $T$.
--
--   Together with Theorem 5.4 this shows that the extra logarithmic factor paid by Algorithm 5 for not knowing $C$ cannot be removed at confidence level $1-1/T$.
--
--   Differences from the source:
--   - generalization: no algorithm can guarantee R_T = O(C) + o(log² T) w.p. ≥ 1 − 1/T (an asymptotic guarantee) → for every learner, every a ≥ 0 and every g = o(log² T): for all sufficiently large T the guarantee at T fails; reason: this implies that no T₀ makes the guarantee hold for all T ≥ T₀; it is what the proof shows (p.32: "for sufficiently large T, no algorithm … can guarantee … (14)")
--   - reading: R_T = O(C) + o(log² T) → R_T ≤ a·C + g(T) with a ≥ 0 a constant and g : ℕ → ℝ, g = o(log² T), not depending on C; reason: the proof fixes "an arbitrary constant a ≥ 0" and treats "any additive term o(log² T) independent of C" (p.34); an additive constant of O(C) is absorbed into g
--   - generalization: the guarantee over all instances and attacks of the model → the guarantee required only for fixed context sequences and attacks fixed in advance (a set S, |S| ≤ C, and measurable maps Y_t = g_t(p_t) on S); reason: a weaker requirement makes the impossibility stronger; the paper states it "even when the attack are required to be fixed in advance" (p.31), and its attack (sale iff p_t ≤ 1/2) is of this form
--   - reading: an algorithm without knowledge of C, even randomized → a price rule π_T(ω, u_{≤t}, Y_{<t}) on any probability space Ω, measurable in ω for each fixed history, depending on T but with no argument C; reason: the standard meaning of a randomized algorithm; deterministic algorithms are the one-point Ω
--   - encoding: even when d = 1 → learners and instances with d = 1: θ⋆ and contexts in the closed unit ball of EuclideanSpace ℝ (Fin 1), v_t ≥ 0; reason: the paper's d = 1 case; the published base model's Θ
--   - encoding: the feedback of the execution → every Y satisfying Y_t = g_t(p_t) on S and Y_t = 𝕀{p_t ≤ v_t} off S for t < T; reason: for an online learner exactly one such Y exists on the rounds t < T
--   - encoding: P(R_T ≤ aC + g(T)) ≥ 1 − 1/T over the learner's randomness → volume on Ω (a probability measure) of {ω | R_T ≤ aC + g(T)} is at least ENNReal.ofReal(1 − 1/T); reason: for an online learner measurable in ω and measurable attack maps the event is measurable, so the measure is its probability
--   - encoding: rounds t = 1, …, T and bits in {0, 1} → rounds 0, …, T − 1 of ℕ-indexed sequences and Bool bits; reason: Lean convention; same instances
-- source:
--   Castiglioni and Stradi, Decoupling Corruption and Horizon in Robust Contextual Pricing, arXiv:2607.11210, Theorem 6.1, p.32 (Equation (14), p.32; attacks fixed in advance, p.31; proof pp.32–34)

import Mathlib
import Definitions.Def_RobustCtxPricing_Model
import Definitions.Def_RobustCtxPricing_Supplement_Learner

open MeasureTheory

namespace RobustCtxPricing.Supplement

/-- **Theorem 6.1.** Castiglioni–Stradi, *Decoupling Corruption and Horizon in Robust Contextual
Pricing*, arXiv:2607.11210, §6, p.32: "No algorithm without knowledge of `C`, even randomized, can
guarantee regret: `R_T = O(C) + o(log² T)`, with probability at least `1 − 1/T` for every
corruption budget `C`, even when `d = 1`."

For every randomized online learner `π` with internal randomness on a probability space `Ω` that is
not given `C` (`IsOnlineLearner`), every constant `a ≥ 0` and every `g : ℕ → ℝ` with
`g(T) = o(log² T)` (independent of `C`), for all sufficiently large horizons `T` the guarantee
"for every `C` and every `d = 1` instance whose attacked rounds (at most `C`, fixed in advance) are
answered by fixed measurable maps of the price, `P(R_T ≤ aC + g(T)) ≥ 1 − 1/T`" fails. In
particular no such `π`, `a`, `g` satisfy the guarantee for all `T ≥ T₀`.

**Formalization Note.** The conclusion "for all large `T`, the guarantee at `T` fails" implies the
negation of the asymptotic guarantee "`∃ T₀, ∀ T ≥ T₀`, the guarantee holds"; it is what the proof
shows (p.32: "for sufficiently large `T`, no algorithm … can guarantee … (14)"). Requiring the
guarantee only against oblivious attacks, measurable attack maps and fixed contexts makes the
impossibility stronger. -/
theorem theorem_6_1 {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (volume : Measure Ω)]
    (π : ℕ → Ω → (ℕ → EuclideanSpace ℝ (Fin 1)) → (ℕ → Bool) → ℕ → ℝ)
    (hπ : IsOnlineLearner π) (a : ℝ) (ha : 0 ≤ a) (g : ℕ → ℝ)
    (hg : g =o[Filter.atTop] fun T : ℕ => Real.log T ^ 2) :
    ∀ᶠ T in Filter.atTop, ¬ HighProbGuarantee π a g T := by sorry

end RobustCtxPricing.Supplement
