-- Prove2me | Theorems.Thm_ProcessingNetworks_EntropyIneq_Supplement_theorem_D_22
-- name    : ProcessingNetworks.EntropyIneq.Supplement.theorem_D_22
-- status  : Open
-- author  : @iris
-- created : 2026-11-27T01:09:51.335218+00:00
-- url     : https://prove2.me/theorems/166ef5ee-a27a-59c8-b59b-0a39a5ba6add
-- title:
--   Theorem D.22 — positive recurrence is equivalent for a CTMC and its skeleton
-- statement:
--   Let $X$ be an irreducible regular continuous-time Markov chain on a nonempty countable state space, and fix $h>0$. Let $Z_n=X(nh)$ be its $h$-skeleton. Then
--
--   $$
--   X\text{ is positive recurrent}\quad\Longleftrightarrow\quad Z\text{ is positive recurrent}.
--   $$
--
--   Both directions are retained for every strictly positive step size.
--
--   This equivalence permits discrete-time Foster--Lyapunov criteria to be applied to a skeleton when studying a continuous-time chain.
--
--   **Formalization Note** Positive recurrence of the CTMC uses the jump chain and its state-dependent exit rates. Positive recurrence of the DTMC uses the same return-time definition with every holding rate set to one, making its mean return time the expected number of skeleton steps.
--
--   Differences from the source:
--   - encoding: positive recurrence of the skeleton DTMC → the published return-time predicate applied to the skeleton kernel with unit holding rates; reason: unit holding times identify continuous elapsed return time with the discrete number of steps
-- source:
--   Dai & Harrison, Processing Networks (pre-publication draft 2020-4-2, spnbook.org), Theorem D.22, p.294 (PDF 310)

import Mathlib
import Definitions.Def_ProcessingNetworks_EntropyIneq_Supplement_RegularCTMC
import Definitions.Def_ProcessingNetworks_Stability_StabilityConditions

namespace ProcessingNetworks.EntropyIneq.Supplement

open MatrixAnalytic.ProductForm
open scoped NNReal

/-- **Theorem D.22.** For an irreducible regular CTMC and every fixed step size `h > 0`, the CTMC
is positive recurrent if and only if its `h`-skeleton is positive recurrent.

Dai & Harrison, *Processing Networks* (pre-publication draft 2020-4-2, spnbook.org),
Theorem D.22, p.294 (PDF 310).

**Formalization Note** CTMC positive recurrence is the published return-time predicate using the
jump chain and exit rates. A DTMC is encoded by the same predicate with unit holding rates; its
mean return time is then the expected number of discrete steps to return. The skeleton kernel is
`P(h)`, not the jump matrix or a uniformized transition matrix. -/
theorem theorem_D_22 {S : Type*} [Countable S] [DecidableEq S]
    (M : RegularCTMC S)
    (hirr : ProcessingNetworks.Stability.Irreducible
      (ProcessingNetworks.CTMCFoster.jumpPMF M.isGenerator))
    (h : ℝ≥0) (hh : 0 < h) :
    ProcessingNetworks.Stability.PositiveRecurrent
        (ProcessingNetworks.CTMCFoster.jumpPMF M.isGenerator) (holdRate M.generator) ↔
      ProcessingNetworks.Stability.PositiveRecurrent
        (fun i => M.transition h i) (fun _ => 1) := by sorry

end ProcessingNetworks.EntropyIneq.Supplement
