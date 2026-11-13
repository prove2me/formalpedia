-- Prove2me | Theorems.Thm_ProcessingNetworks_CTMCFoster_theorem_D_27
-- name    : ProcessingNetworks.CTMCFoster.theorem_D_27
-- status  : Proved
-- author  : @iris
-- created : 2026-10-31T13:27:36.964416+00:00
-- url     : https://prove2.me/theorems/61595cb9-86fe-49a7-a6c4-fa663699cc61
-- title:
--   Theorem D.27 — Foster–Lyapunov criterion for continuous-time Markov chains
-- statement:
--   Let $X$ be an irreducible continuous-time Markov chain on a countable state space $\mathscr S$ with generator matrix $\Lambda$ and exit rates $\lambda(i)=-\Lambda_{ii}>0$, and assume its transition rates are bounded:
--
--   $$
--   \sup_{i\in\mathscr S}\lambda(i)<\infty.
--   $$
--
--   Assume there exist constants $b>0$ and $c>0$, a finite set $C\subset\mathscr S$, and a non-negative function $V:\mathscr S\to\mathbb R_+$ such that
--
--   $$
--   \Lambda V(i)\le -c+b\,1_C(i),\qquad i\in\mathscr S.
--   $$
--
--   Then $X$ is positive recurrent with a unique stationary distribution.
--
--   This criterion reduces the stability of a bounded-rate Markov model to exhibiting one Lyapunov function. It is the standard continuous-time tool for the Markov representations of processing networks.
--
--   Differences from the source:
--   - encoding: the state space is nonempty by convention → `[Nonempty S]`; reason: on an empty type every hypothesis holds and there is no distribution
--   - encoding: a CTMC with generator $\Lambda$ → the generator, with `IsGeneratorC Λ` (Definition D.1 with (D.2)) and the published predicates of its jump matrix and exit rates; reason: every notion in the statement depends on the process only through $\Lambda$
--   - encoding: (D.36) as a real inequality → `DriftConditionAt`, which also asserts convergence of the row; reason: a real `tsum` of a divergent series is $0$ in Lean; for $V\ge0$ divergence means the value $+\infty$, which fails the printed inequality
--   - encoding: $X$ positive recurrent → `Stability.PositiveRecurrent`, recurrence of the jump chain plus $\mathbb E_i(T_i)<\infty$ at every state; reason: Definitions D.7 and D.15, in the published form
--   - encoding: the standing assumption that every generator is regular (Definition D.3, p.289), i.e. non-explosive → no non-explosion hypothesis; reason: (D.28) is a hypothesis, and the book notes on p.289 that (D.8) = (D.28) is sufficient for non-explosion, so no instance of the book's theorem is lost or added
-- source:
--   Dai & Harrison, Processing Networks (pre-publication draft 2020-4-2, spnbook.org), Theorem D.27, eq. (D.36), p.298 (PDF 314), with (D.28), p.296 (PDF 312)

import Mathlib
import Definitions.Def_MatrixAnalytic_ProductForm_Chain
import Definitions.Def_ProcessingNetworks_Stability_StabilityConditions
import Definitions.Def_ProcessingNetworks_CTMCFoster_jumpPMF
import Definitions.Def_ProcessingNetworks_CTMCFoster_DriftConditionAt

namespace ProcessingNetworks.CTMCFoster

open MatrixAnalytic.ProductForm

/-- Theorem D.27 (Foster–Lyapunov criterion for CTMC). Let `X` be an irreducible continuous-time
Markov chain on a countable state space `S` with bounded transition rates (D.28). If there are
constants `b > 0`, `c > 0`, a finite set `C ⊆ S` and a non-negative function `V` with
`ΛV(i) ≤ -c + b 1_C(i)` for every `i` (D.36), then `X` is positive recurrent with a unique
stationary distribution.

Dai & Harrison, Processing Networks (pre-publication draft 2020-4-2, spnbook.org), Theorem D.27,
eq. (D.36), p.298 (PDF 314), with (D.28), p.296 (PDF 312).

**Formalization Note** The chain is its generator: `IsGeneratorC Λ` is Definition D.1 with (D.2).
No non-explosion hypothesis is taken, since (D.28) implies it (p.289). `Nonempty S` is needed: on
an empty type there is no distribution, while every hypothesis holds. -/
theorem theorem_D_27 {S : Type*} [Countable S] [Nonempty S] [DecidableEq S] {Λ : S → S → ℝ}
    (hΛ : IsGeneratorC Λ) (hirr : Stability.Irreducible (jumpPMF hΛ))
    (hbdd : BddAbove (Set.range (holdRate Λ)))
    (b c : ℝ) (hb : 0 < b) (hc : 0 < c) (C : Set S) (hC : C.Finite)
    (V : S → ℝ) (hV : ∀ i, 0 ≤ V i) (hdrift : ∀ i, DriftConditionAt Λ V b c C i) :
    Stability.PositiveRecurrent (jumpPMF hΛ) (holdRate Λ) ∧
      Stability.HasUniqueStationaryDistribution (jumpPMF hΛ) (holdRate Λ) := by sorry

end ProcessingNetworks.CTMCFoster
