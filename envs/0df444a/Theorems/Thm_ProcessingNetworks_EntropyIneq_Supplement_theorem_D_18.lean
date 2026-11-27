-- Prove2me | Theorems.Thm_ProcessingNetworks_EntropyIneq_Supplement_theorem_D_18
-- name    : ProcessingNetworks.EntropyIneq.Supplement.theorem_D_18
-- status  : Open
-- author  : @iris
-- created : 2026-11-27T01:08:50.392895+00:00
-- url     : https://prove2.me/theorems/b9998dc6-3199-4ddb-8fa4-617de71af8cc
-- title:
--   Theorem D.18 — stationary initial law makes the CTMC stationary
-- statement:
--   Let $X$ be an irreducible regular continuous-time Markov chain on a nonempty countable state space. Let $\pi$ be a stationary distribution and suppose that $X(0)$ has distribution $\pi$. Then
--
--   $$
--   \mathcal L(X(t))=\pi\qquad(t\ge 0),
--   $$
--
--   and the whole process is stationary: for every finite ordered list $0\le t_0\le\cdots\le t_n$, every $c\ge0$, and every state tuple $(x_0,\ldots,x_n)$, the probability of $(X(t_0),\ldots,X(t_n))=(x_0,\ldots,x_n)$ equals the corresponding probability after replacing every $t_k$ by $t_k+c$.
--
--   The second conclusion is stronger than equality of one-time marginals only in the sense intended by the book: it spells out the phrase "stationary process."
--
--   **Formalization Note** Finite-dimensional probabilities are written using the initial law and the Markov transition products. Equal adjacent times are allowed. The state space remains countable and may be infinite.
--
--   Differences from the source:
--   - encoding: X is a stationary process → every finite-dimensional distribution at ordered nonnegative times is invariant under every common nonnegative shift; reason: this is the standard definition of strict stationarity and states the book's whole-process conclusion explicitly
--   - encoding: X(t) has distribution π for each t > 0 → for each t ≥ 0; reason: the added case t = 0 is the hypothesis that X(0) has distribution π, so no instance or content changes
-- source:
--   Dai & Harrison, Processing Networks (pre-publication draft 2020-4-2, spnbook.org), Theorem D.18, p.293 (PDF 309), continuing p.294 (PDF 310)

import Mathlib
import Definitions.Def_ProcessingNetworks_EntropyIneq_Supplement_RegularCTMC
import Definitions.Def_ProcessingNetworks_Stability_StabilityConditions

namespace ProcessingNetworks.EntropyIneq.Supplement

open MatrixAnalytic.ProductForm
open scoped ENNReal NNReal

/-- **Theorem D.18.** If an irreducible regular CTMC is started in a stationary distribution
`π`, every one-time marginal is `π` and all of its finite-dimensional distributions are invariant
under a common nonnegative time shift.

Dai & Harrison, *Processing Networks* (pre-publication draft 2020-4-2, spnbook.org),
Theorem D.18, p.293 (PDF 309), continuing on p.294 (PDF 310).

**Formalization Note** Stationarity of the whole process is stated literally as invariance of every
finite-dimensional distribution. For ordered times `t₀ ≤ ⋯ ≤ tₙ`, the displayed product is the
Markov cylinder probability of the state tuple `x`; quantifying over every `n`, ordered `t`, tuple
`x`, and shift `c` is equality of all finite-dimensional laws. The countable state space is not
restricted to a finite one. -/
theorem theorem_D_18 {S : Type*} [Countable S] [DecidableEq S]
    (M : RegularCTMC S)
    (hirr : ProcessingNetworks.Stability.Irreducible
      (ProcessingNetworks.CTMCFoster.jumpPMF M.isGenerator))
    (pi : PMF S)
    (hpi : ProcessingNetworks.Stability.IsStationaryDistribution
      (ProcessingNetworks.CTMCFoster.jumpPMF M.isGenerator)
      (holdRate M.generator) pi)
    (hinit : M.initial = pi) :
    (∀ t : ℝ≥0, M.initial.bind (M.transition t) = pi) ∧
      ∀ (n : ℕ) (t : Fin (n + 1) → ℝ≥0), Monotone t →
        ∀ (c : ℝ≥0) (x : Fin (n + 1) → S),
          (M.initial.bind (M.transition (t 0))) (x 0) *
              ∏ k : Fin n, M.transition (t k.succ - t k.castSucc)
                (x k.castSucc) (x k.succ) =
            (M.initial.bind (M.transition (t 0 + c))) (x 0) *
              ∏ k : Fin n, M.transition ((t k.succ + c) - (t k.castSucc + c))
                (x k.castSucc) (x k.succ) := by sorry

end ProcessingNetworks.EntropyIneq.Supplement
