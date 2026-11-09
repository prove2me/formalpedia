-- Prove2me | Theorems.Thm_PagingDelay_PMD_lemma_2
-- name    : PagingDelay.PMD.lemma_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:49:18.706528+00:00
-- url     : https://prove2.me/theorems/ec5c4410-c6f6-4e5d-98b1-9560a695c29f
-- title:
--   Lemma 2 — feasibility and service of every request
-- statement:
--   For every valid instance, normalized dyadic weights, initial cache, designated outside page and tie order, PMD maintains
--
--   $$x\in[\delta,1]^n,\qquad \sum_i x_i\ge n-k,\qquad B_W\ge0.$$
--
--   These inequalities hold at the initial state and every recorded transient state; the continuous critical paths remain in the mass-$n-k$ state space as well. Equality of total antimass holds after critical services, after closing each hole and between complete services. Every request has a finite attained serving time. This includes both parts (a) and (b) of the source lemma.
--
--   Differences from the source:
--   - encoding: finite pages, continuous time, finite requests and instantaneous cache walks → Fin n pages, real times, finite request and event lists, and ENNReal costs; reason: same instances; positive weights reduce every finite-cost offline schedule to finitely many fetches without increasing cost
--   - reading: any tie-breaking rule suffices → all page orders π and all designated initial pages i₀ outside O₀; reason: an arbitrary order resolves simultaneous critical times and equal effective deadlines; no order is fixed
--   - encoding: Algorithm 1 with instantaneous services and eventual service → explicit transition recursion with |σ|+1 next-event iterations, transient states, optional infima and zero-denominator guards; reason: each critical service serves a pending request, so there are at most |σ|; the guards only totalize undefined inputs, and Lemma 2 states full service rather than assuming it
--   - encoding: the first nonnegative hitting time |λ| and natural logarithm L → guarded real infimum and L = log(2k+1); reason: on the stated valid domain the hitting set is nonempty, bounded below and closed; k≥1 makes L positive
-- source:
--   Julian Born, Yann Disser, Linda Thelen, Tight weighted paging with delay via mirror descent, STOC 2027 submission #453 (October 2026), Lemma 2 — feasibility and service of every request, p. 10. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/453.pdf

import Definitions.Def_PagingDelay_PMD_Algorithm

namespace PagingDelay.PMD
open scoped BigOperators

/-- Julian Born, Yann Disser, Linda Thelen, Tight weighted paging with delay via mirror descent, STOC 2027 submission #453 (October 2026), Lemma 2 — feasibility and service of every request, p. 10. -/
theorem lemma_2 (n k : ℕ) (hk : 1 ≤ k) (hkn : k < n)
    (w : Fin n → ℝ) (hw : PMDWeights w)
    (O₀ : Finset (Fin n)) (hO₀ : O₀.card = k)
    (i₀ : Fin n) (hi₀ : i₀ ∉ O₀) (π : Fin n ≃ Fin n)
    (σ : Instance n) (hσ : ValidInstance σ) :
    let e := run k w O₀ i₀ π σ
    (∀ s ∈ e.initial :: e.moves.map (fun m => m.after),
      (∀ i, delta k ≤ s.x i ∧ s.x i ≤ 1) ∧
      (n : ℝ) - k ≤ ∑ i, s.x i ∧ ∀ j, 0 ≤ s.budget j) ∧
    (∑ i, e.current.x i) = (n : ℝ) - k ∧
    (∀ m ∈ e.moves, (match m.kind with
      | .critical _ => True | .closeHole _ => True | _ => False) →
      ∑ i, m.after.x i = (n : ℝ) - k) ∧
    (∀ m ∈ e.moves, ∀ p, m.kind = .critical p →
      ∀ s ∈ Set.Icc 0 (pathLength k w m.before.x p),
        StateValid k (path k w m.before.x p s)) ∧
    (∀ r ∈ σ, ∃ t, fractionalService k e r = some t) := by sorry

end PagingDelay.PMD
