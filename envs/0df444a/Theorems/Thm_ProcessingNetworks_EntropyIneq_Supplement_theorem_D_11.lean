-- Prove2me | Theorems.Thm_ProcessingNetworks_EntropyIneq_Supplement_theorem_D_11
-- name    : ProcessingNetworks.EntropyIneq.Supplement.theorem_D_11
-- status  : Open
-- author  : @iris
-- created : 2026-11-27T01:08:15.19673+00:00
-- url     : https://prove2.me/theorems/764ece61-1159-4ab9-b0a7-88e550f63d89
-- title:
--   Theorem D.11 — invariant measure unique up to scale
-- statement:
--   Let $X$ be a regular continuous-time Markov chain on a nonempty countable state space, with generator $\Lambda$ and jump matrix $G$. Assume that $X$ is irreducible and recurrent. Then there is a nonzero nonnegative vector $\eta$ such that
--
--   $$
--   \eta\Lambda=0.
--   $$
--
--   Moreover, if $\eta'$ is any other nonnegative invariant measure, then $\eta'=c\eta$ for some $c\ge 0$. Thus the invariant measure is unique up to scale; it is not asserted to be a probability distribution.
--
--   This is the invariant-measure existence and uniqueness result used to relate recurrent generators to their jump chains.
--
--   **Formalization Note** Convergence of every coordinate series in $\eta\Lambda$ is part of the published invariant-measure predicate. Recurrence and irreducibility are those of the jump chain, as in Definitions D.7 and D.10. The scalar $c=0$ includes the zero invariant measure.
--
--   Differences from the source:
--   - encoding: an invariant measure unique up to a constant → a nonzero nonnegative invariant vector whose every nonnegative invariant vector is a nonnegative scalar multiple; reason: this makes the standard meaning of uniqueness up to scale explicit and includes the zero measure with scalar zero
-- source:
--   Dai & Harrison, Processing Networks (pre-publication draft 2020-4-2, spnbook.org), Theorem D.11, p.291 (PDF 307)

import Mathlib
import Definitions.Def_ProcessingNetworks_EntropyIneq_Supplement_RegularCTMC
import Definitions.Def_ProcessingNetworks_CTMCFoster_IsInvariantMeasure
import Definitions.Def_ProcessingNetworks_Stability_StabilityConditions

namespace ProcessingNetworks.EntropyIneq.Supplement

open MatrixAnalytic.ProductForm

/-- **Theorem D.11.** An irreducible recurrent regular generator has a nonzero invariant measure,
unique up to multiplication by a nonnegative constant.

Dai & Harrison, *Processing Networks* (pre-publication draft 2020-4-2, spnbook.org),
Theorem D.11, p.291 (PDF 307).

**Formalization Note** A measure is the book's nonnegative real vector, not necessarily normalized.
The distinguished invariant measure is required to be nonzero. The uniqueness clause also covers
the zero invariant measure, with scalar `c = 0`. Recurrence and irreducibility are those of the
jump chain, exactly as in Definitions D.7 and D.10. -/
theorem theorem_D_11 {S : Type*} [Countable S] [DecidableEq S]
    (M : RegularCTMC S)
    (hirr : ProcessingNetworks.Stability.Irreducible
      (ProcessingNetworks.CTMCFoster.jumpPMF M.isGenerator))
    (hrec : ∀ i, ProcessingNetworks.Stability.Recurrent
      (ProcessingNetworks.CTMCFoster.jumpPMF M.isGenerator) i) :
    ∃ η : S → ℝ,
      (∀ i, 0 ≤ η i) ∧ η ≠ 0 ∧
      ProcessingNetworks.CTMCFoster.IsInvariantMeasure M.generator η ∧
      ∀ η' : S → ℝ, (∀ i, 0 ≤ η' i) →
        ProcessingNetworks.CTMCFoster.IsInvariantMeasure M.generator η' →
        ∃ c : ℝ, 0 ≤ c ∧ η' = fun i => c * η i := by sorry

end ProcessingNetworks.EntropyIneq.Supplement
