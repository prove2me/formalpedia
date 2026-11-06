-- Prove2me | Theorems.Thm_TIESched_lemma_3_3
-- name    : TIESched.lemma_3_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T00:47:09.124188+00:00
-- url     : https://prove2.me/theorems/3c00e115-9fb0-45c1-b5dc-3a9909728a24
-- title:
--   Lemma 3.3 — bounded interaction reduction
-- statement:
--   Let $M$ be a feasible, truthful, $\Gamma$-approximate fractional mechanism family. For every $\delta>0$ there is a feasible, truthful fractional mechanism family $M^\delta$ of interaction order at most $m-1$ such that
--   $$C\big(p,x^{S,\delta}(p)\big)\le\Gamma\big(\mathrm{OPT}(p)+|S|\delta\big)$$
--   for every instance $(S,p)$, i.e. every finite job set $S$ and nonnegative report $p$.
--
--   This is the reduction half of the proof of Theorem 1.
--
--   Differences from the source:
--   - generalization: M^δ is a fractional mechanism family → M^δ is also truthful; reason: step (1) on p.10 announces a truthful replacement and Lemma 5.13 delivers it; the Lean statement implies the source's
--   - encoding: rules x^S, π^S on ℝ^{m×S}_{≥0} with values in X(S) → total functions on ℝ^{m×S}, with feasibility a separate predicate on nonnegative reports; reason: a family on the orthant extends to such a total function, and the hypotheses read nonnegative reports only
-- source:
--   Wang, Xu, Zhang, Tight Analysis of Randomized Truthful Scheduling: An (m+1)/2 Lower Bound, arXiv:2611.05142 (artifact sha256 a89db2da…), Lemma 3.3, p.11

import Mathlib
import Definitions.Def_TIESched_interaction

set_option autoImplicit false

namespace TIESched

/-- **Lemma 3.3 (Bounded interaction reduction)** (Wang, Xu, Zhang, arXiv:2611.05142, Lemma 3.3,
p.11). Let `M = (x^S, π^S)_S` be a truthful, Γ-approximate fractional mechanism family. For every
`δ > 0` there is a fractional mechanism family `M^δ = (x^{S,δ}, π^{S,δ})_S` of interaction order at
most `m − 1` such that `C(p, x^{S,δ}(p)) ≤ Γ(OPT(p) + |S|δ)` for every instance `(S, p)`.

**Formalization Note.** `M^δ` is a fractional mechanism family, so its allocation is feasible; the
statement also asserts that `M^δ` is truthful (as in step (1) of §3.2, p.10). An instance is any
finite job set with a nonnegative report. -/
theorem lemma_3_3 (m : ℕ) [NeZero m] (hm : 2 ≤ m) (Γ : ℝ) (M : FracMech m)
    (hfeas : Feasible M.alloc) (htr : Truthful M) (happ : IsApprox M Γ) (δ : ℝ) (hδ : 0 < δ) :
    ∃ Mδ : FracMech m, Feasible Mδ.alloc ∧ Truthful Mδ ∧ HasInteractionOrderLE Mδ.alloc (m - 1) ∧
      ∀ (S : Finset ℕ) (p : Fin m → S → ℝ), IsNonneg p →
        makespan p (Mδ.alloc S p) ≤ Γ * (OPT p + (S.card : ℝ) * δ) := by sorry

end TIESched
