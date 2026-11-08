-- Prove2me | Theorems.Thm_TightClock_lemma_6_5
-- name    : TightClock.lemma_6_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T05:20:42.752107+00:00
-- url     : https://prove2.me/theorems/6b276c91-d2dc-4c3f-914d-5a854758a76d
-- title:
--   Lemma 6.5 — account calibration
-- statement:
--   Fix a realized tree and a single-step clock, with state $J^t$ and history $H^t$. At the initial state,
--
--   $$\log A_{\mathrm{root}}(J^0)\le(e^a-1)B,$$
--
--   and for every leaf $S$ and every step $t$,
--
--   $$\mathbb E\Big[\sum_{i\in S\text{ active}}X_i\ \Big|\ H^t\Big]\le\frac{\log A_S(J^t)+a^2B}{a(1-a)}.$$
--
--   So the root's account is initially small, and a leaf's account bounds the conditional expected welfare of its active bidders.
--
--   Differences from the source:
--   - encoding: the depth $L$ of the tree, with levels $r=1,\dots,L$ in Instance 11 → the hypothesis `1 ≤ L`; reason: at $L=0$ there are no bidders and $h=a^2B/L$ divides by zero; the page's construction has $L\ge1$
--   - encoding: a clock auction after the §6.2 reduction, with tree and seed part of $H^t$ → a valid deterministic `SingleStepStrategy`, with tree and seed fixed parameters; reason: the seed and the tree are fixed before the conditioning, as in the proof of Proposition 6.11; the prior is independent of both
--   - encoding: $\mathbb E[\cdot\mid H^t]$ → `condExpect`, the ratio of two finite sums, at a history $h$ of positive probability; reason: the law is finite, and a history of probability zero is not conditioned on
-- source:
--   Afshinmehr, Ascher, Ashuri, Gkatzelis, Mahmoudkhan, Rubinstein, Schoepflin, Tight Approximation Bounds for Clock Auctions, manuscript (STOC 2027 submission; held artifact sha256 29bccd9c…b31b, preprint basis), Lemma 6.5, §6.4, p.40 (PDF p.43)

import Mathlib
import Definitions.Def_TightClock_account
import Definitions.Def_TightClock_rootNode
import Definitions.Def_TightClock_initialState
import Definitions.Def_TightClock_leafNode
import Definitions.Def_TightClock_familyOf
import Definitions.Def_TightClock_hardPrior
import Definitions.Def_TightClock_IsValidSingleStep
import Definitions.Def_TightClock_condExpect

set_option autoImplicit false

namespace TightClock

open Classical in
/-- Lemma 6.5 (Account calibration), p.40 (PDF 43), of Afshinmehr et al., manuscript (STOC 2027 submission):
`log A_root(J⁰) ≤ (eᵃ − 1) B`, and for every leaf `S` and every step `t`,
`E[∑_{i ∈ S active} Xᵢ | Hᵗ] ≤ (log A_S(Jᵗ) + a² B) / (a (1 − a))`. -/
theorem lemma_6_5 (q L : ℕ) (hq : 8 ≤ q) (hL : 1 ≤ L) (T : Tree q L) :
    Real.log (account T (rootNode q L) (initialState q L)) ≤ (Real.exp (a q) - 1) * (B L : ℝ) ∧
    ∀ (σ : SingleStepStrategy (bidderCount q L)), IsValidSingleStep q L (familyOf T) σ →
      ∀ (s : Path q L L) (h : SingleStepHistory (bidderCount q L)),
        0 < histProb q L (hardPrior q L hq hL) σ h →
        condExpect q L (hardPrior q L hq hL) σ h
            (fun v => ∑ i ∈ (nodeSet T (leafNode s)).filter (fun i => stateOf q L h i ≠ none), v i) ≤
          (Real.log (account T (leafNode s) (stateOf q L h)) + (a q) ^ 2 * (B L : ℝ)) /
            (a q * (1 - a q)) := by sorry

end TightClock
