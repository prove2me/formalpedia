-- Prove2me | Theorems.Thm_ProcessingNetworks_EntropyIneq_Supplement_lemma_D_23
-- name    : ProcessingNetworks.EntropyIneq.Supplement.lemma_D_23
-- status  : Open
-- author  : @iris
-- created : 2026-11-27T01:10:10.160803+00:00
-- url     : https://prove2.me/theorems/1d642af2-f17a-581b-8f20-5be4f68e3dcc
-- title:
--   Lemma D.23 — exit-rate continuity bound for transition probabilities
-- statement:
--   Let $P(t)=(P_{ij}(t))$ be the transition semigroup of a regular continuous-time Markov chain with generator $\Lambda$, and let $\lambda(i)=-\Lambda_{ii}$ be the exit rate from state $i$. For every pair of states $i,j$ and all $t,h\ge0$,
--
--   $$
--   \left|P_{ij}(t+h)-P_{ij}(t)\right|\le 1-e^{-\lambda(i)h}.
--   $$
--
--   The modulus depends on the starting-state exit rate, with no global bounded-rate hypothesis.
--
--   This estimate supplies the uniform continuity needed to pass from convergence at skeleton times to convergence at every continuous time.
--
--   **Formalization Note** Nonnegative times are represented by $\mathbb R_{\ge0}$. PMF coordinates are converted to real probabilities; this conversion is exact because every coordinate lies in $[0,1]$.
--
--   Differences from the source:
--   - encoding: real times constrained by t,h ≥ 0 and probability coordinates → times in the nonnegative-real type and PMF coordinates converted exactly to real numbers; reason: the types enforce the source's domain and probabilities are finite
-- source:
--   Dai & Harrison, Processing Networks (pre-publication draft 2020-4-2, spnbook.org), Lemma D.23, p.295 (PDF 311)

import Mathlib
import Definitions.Def_ProcessingNetworks_EntropyIneq_Supplement_RegularCTMC

namespace ProcessingNetworks.EntropyIneq.Supplement

open MatrixAnalytic.ProductForm
open scoped NNReal

/-- **Lemma D.23.** For the transition semigroup of a regular CTMC, every transition coordinate
has the explicit uniform-continuity modulus determined by the exit rate of its starting state:
`|Pᵢⱼ(t+h) - Pᵢⱼ(t)| ≤ 1 - exp(-λ(i)h)`.

Dai & Harrison, *Processing Networks* (pre-publication draft 2020-4-2, spnbook.org),
Lemma D.23, p.295 (PDF 311).

**Formalization Note** Both times range over `ℝ≥0`, so the book's conditions `t,h ≥ 0` are in the
types. PMF coordinates are converted to real numbers without loss because they are at most one.
The rate is the starting-state rate `λ(i) = -Λᵢᵢ`, not a global bound. -/
theorem lemma_D_23 {S : Type*} [Countable S] [DecidableEq S]
    (M : RegularCTMC S) (i j : S) (t h : ℝ≥0) :
    |(M.transition (t + h) i j).toReal - (M.transition t i j).toReal| ≤
      1 - Real.exp (-(holdRate M.generator i) * (h : ℝ)) := by sorry

end ProcessingNetworks.EntropyIneq.Supplement
