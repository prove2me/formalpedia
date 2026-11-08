-- Prove2me | Theorems.Thm_TightClock_single_step_reduction
-- name    : TightClock.single_step_reduction
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T05:18:48.526659+00:00
-- url     : https://prove2.me/theorems/0836b125-9078-4343-addc-88af3743610c
-- title:
--   §6.2 — every clock reduces to a single-step clock
-- statement:
--   Consider the instance of §6.2 with parameters $q\ge8$, $L\ge1$ and a realized tree with family $\mathcal F$. For every valid deterministic clock $\sigma$ for $\mathcal F$, there is a valid single-step clock $\sigma'$ for $\mathcal F$ such that every run of $\sigma'$ on a nonnegative profile stops within $nL$ steps, and
--
--   $$\mathbb E_{X\sim D}[\mathrm{SW}_\sigma(X)]\le\mathbb E_{X\sim D}[\mathrm{SW}_{\sigma'}(X)].$$
--
--   This is the bridge from the clock class of §3 and §6.1, with arbitrary prices and unbounded rounds, to the coin-toss analysis of §6.4–§6.6.
--
--   **Formalization Note** The clock $\sigma$ has arbitrary real prices, and it may never stop.
--
--   Differences from the source:
--   - encoding: the depth $L$ of the tree, with levels $r=1,\dots,L$ in Instance 11 → the hypothesis `1 ≤ L`; reason: at $L=0$ there are no bidders and $h=a^2B/L$ divides by zero; the page's construction has $L\ge1$
--   - encoding: "every clock auction", with a random seed → a deterministic clock, that is one seed; reason: the proof of Proposition 6.11 fixes the seed first ("Fix the auction's random seed"), and the randomized statement is Proposition 6.11 itself
--   - encoding: "every run has at most $nL$ steps" → every run from a nonnegative profile reaches `stop` at some step $t\le nL$; reason: a stop at step $t$ means exactly $t$ tests were made
-- source:
--   Afshinmehr, Ascher, Ashuri, Gkatzelis, Mahmoudkhan, Rubinstein, Schoepflin, Tight Approximation Bounds for Clock Auctions, manuscript (STOC 2027 submission; held artifact sha256 29bccd9c…b31b, preprint basis), §6.2, "Price tests are coin tosses", p.35 (PDF p.38)

import Mathlib
import Definitions.Def_TightClock_familyOf
import Definitions.Def_TightClock_hardPrior
import Definitions.Def_TightClock_IsValidClock
import Definitions.Def_TightClock_clockWelfare
import Definitions.Def_TightClock_priorExpect
import Definitions.Def_TightClock_IsValidSingleStep
import Definitions.Def_TightClock_ssWelfare

set_option autoImplicit false

namespace TightClock

/-- §6.2, "Price tests are coin tosses", p.35 (PDF 38), of Afshinmehr et al., manuscript (STOC 2027 submission): on the
instance, every clock auction is dominated by a single-step clock, every run of which has at most `nL` steps.
It is stated for a deterministic clock, that is for a fixed seed, as used in the proof of Proposition 6.11.

**Formalization Note** The clock `σ` has arbitrary real prices and unbounded rounds, and it may never stop. -/
theorem single_step_reduction (q L : ℕ) (hq : 8 ≤ q) (hL : 1 ≤ L) (T : Tree q L)
    (σ : Strategy (bidderCount q L)) (hσ : IsValidClock (familyOf T) σ) :
    ∃ σ' : SingleStepStrategy (bidderCount q L),
      IsValidSingleStep q L (familyOf T) σ' ∧
      (∀ v : Fin (bidderCount q L) → ℝ, (∀ i, 0 ≤ v i) →
        ∃ t, t ≤ bidderCount q L * L ∧ ∃ S, σ' (ssHist q L σ' v t) = .stop S) ∧
      priorExpect (hardPrior q L hq hL) (clockWelfare σ) ≤
        priorExpect (hardPrior q L hq hL) (ssWelfare q L σ') := by sorry

end TightClock
