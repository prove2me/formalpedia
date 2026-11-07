-- Prove2me | Theorems.Thm_RGMISFast_lemma_3_1
-- name    : RGMISFast.lemma_3_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T11:31:40.438209+00:00
-- url     : https://prove2.me/theorems/318cf82a-d15d-47a5-8bb7-d2a83a1d2cc3
-- title:
--   Lemma 3.1: entries and growth, (9) and (10) w.p. $\ge1-320e^{-L}$
-- statement:
--   Let $G$ be a finite simple graph with all degrees at most $\Delta\ge2$ and root $u^*$, with i.i.d. Exp(1) ranks, and fix a deviation parameter $L\ge8$. With probability at least $1-320e^{-L}$, both of the following hold:
--
--   1. for every $0\le i<m\le M$ and every root-connected set $B$ active at $a_m$,
--   $$
--   K_{m,i}(B)\le 32c^{1+m-i}\big(2S_m(B)+L\big); \tag{9}
--   $$
--   2. for every $1\le m\le M$ and every root-connected set $A$ active at $a_m$,
--   $$
--   |\Gamma_m(A)|\le 2S_m(A)+L. \tag{10}
--   $$
--
--   These are the entry and growth estimates behind the recurrence of Proposition 4.1.
--
--   **Formalization Note** One failure event for (9) and (10) jointly, of measure at most $320e^{-L}$ under the product Exp(1) law. $\Delta$ fixes $M$ through (6).
--
--   Differences from the source:
--   - encoding: with probability at least 1 − 320e^{−L} → the (outer) measure of the failure set is at most 320e^{−L}; reason: equivalent for a probability measure
-- source:
--   Dalirrooyfard, Makarychev, Mitrović, Ramachandran, Randomized Greedy MIS Is Fast at Every Node, STOC 2027 submission (manuscript sha256 e93cdfecc03618969d5f2ecf8171c6f84c528edcc473b2f864299e555f823664), Lemma 3.1, eqs. (9)–(10), p.14 (PDF p.16); proof in §6.2, pp.24–25

import Mathlib
import Definitions.Def_RGMISFast_GoodEvent
import Definitions.Def_RGMISFast_rankLaw

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace RGMISFast

/-- Lemma 3.1 (Entries and Growth; Dalirrooyfard, Makarychev, Mitrović, Ramachandran, *Randomized Greedy MIS Is Fast at Every Node*,
STOC 2027 submission (manuscript sha256 e93cdfec…), p.14, proof in §6.2): fix a deviation parameter
`L ≥ 8`; with probability at least `1 − 320e^{−L}`, both (a) for every `0 ≤ i < m ≤ M` and every
root-connected `B` active at `a_m`, `K_{m,i}(B) ≤ 32c^{1+m−i}(2S_m(B) + L)` (9), and (b) for every
`1 ≤ m ≤ M` and every root-connected `A` active at `a_m`, `|Γ_m(A)| ≤ 2S_m(A) + L` (10), hold.

**Formalization Note** One bad event for (a) and (b) jointly, of (outer) measure at most
`320e^{−L}` under the i.i.d. Exp(1) rank law. `M = Mof Δ`; all degrees at most `∆`, `∆ ≥ 2`
(the setting of Theorem 1.1, which fixes `M`). -/
theorem lemma_3_1 {V : Type*} [Fintype V] [LinearOrder V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (Δ : ℕ) (hΔ : 2 ≤ Δ) (hdeg : ∀ v, G.degree v ≤ Δ) (u : V) (L : ℝ)
    (hL : 8 ≤ L) :
    rankLaw V {r | ¬ (EntryEvent G Δ u L r ∧ GrowthEvent G Δ u L r)} ≤
      ENNReal.ofReal (320 * Real.exp (-L)) := by sorry

end RGMISFast
