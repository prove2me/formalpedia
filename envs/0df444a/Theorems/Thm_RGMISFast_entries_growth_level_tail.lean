-- Prove2me | Theorems.Thm_RGMISFast_entries_growth_level_tail
-- name    : RGMISFast.entries_growth_level_tail
-- status  : Proved
-- author  : @srikkanthr
-- created : 2026-11-15T22:45:43.501417+00:00
-- url     : https://prove2.me/theorems/cf2155e2-0490-4182-aa20-1c8837350b84
-- title:
--   Entries and growth: failure probability at a single rank level
-- statement:
--   Fix the setting of Lemma 3.1, with deviation parameter $L\ge8$, degree bound $\Delta\ge2$, a fixed root, and a level $1\le m\le M$. The probability that any growth or boundary inequality fails at that level is at most
--   $$
--   (m+1)(e^{-2}+2e^{-4})a_m e^{-L}.
--   $$
--   The growth failure means that some root-connected set active at $a_m$ has $|\Gamma_m(A)|>2S_m(A)+L$. A boundary failure means that for some parent index $i<m$, some root-connected set active at $a_m$ has
--   $$
--   K_{m,i}(B)>32c^{1+m-i}(2S_m(B)+L).
--   $$
--   This is the fixed-level probability estimate used in the first line of Equation (31), following Equation (30). It keeps the factor $a_m$ needed to sum uniformly over all levels. The sum over levels and the constant $320$ are proved separately.
-- source:
--   Dalirrooyfard, Makarychev, Mitrović, Ramachandran, Randomized Greedy MIS Is Fast at Every Node, §6.2, proof of Lemma 3.1, Equations (30)–(31), printed p.25 (PDF p.27), manuscript sha256 e93cdfecc03618969d5f2ecf8171c6f84c528edcc473b2f864299e555f823664. The fixed-level estimate after applying Markov and the union bound to one growth event and m boundary events.

import Definitions.Def_RGMISFast_GoodEvent
import Definitions.Def_RGMISFast_rankLaw
open MeasureTheory ProbabilityTheory RGMISFast
open scoped ENNReal
set_option autoImplicit false

theorem RGMISFast.entries_growth_level_tail {V : Type*} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (Δ : ℕ) (hΔ : 2 ≤ Δ)
    (hdeg : ∀ v, G.degree v ≤ Δ) (u : V) (L : ℝ) (hL : 8 ≤ L)
    (m : ℕ) (hm : 1 ≤ m) (hmM : m ≤ Mof Δ) :
    rankLaw V {r | (∃ A : Finset V, IsRootConnected G u A ∧ ActiveAt G r (am m) A ∧
        2*Sm r A m+L < ((Gammam G r m A).card:ℝ)) ∨
      (∃ i : ℕ, i < m ∧ ∃ B : Finset V, IsRootConnected G u B ∧ ActiveAt G r (am m) B ∧
        32*c^(1+m-i)*(2*Sm r B m+L) < (Kmi G r m i B:ℝ))} ≤
      ENNReal.ofReal (((m:ℝ)+1)*(Real.exp (-2)+2*Real.exp (-4))*am m*Real.exp (-L)) := by sorry
