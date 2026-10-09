-- Prove2me | Theorems.Thm_UnitCapMCF_Excess_lemma5_band_is_cut
-- name    : UnitCapMCF.Excess.lemma5_band_is_cut
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T18:31:43.828353+00:00
-- url     : https://prove2.me/theorems/5b6cd390-b9f2-4fc3-9835-9967a6e181d6
-- title:
--   Proof of Lemma 5, p. 410 — every level band Aᵢ is a cut
-- statement:
--   At a cost scale $\varepsilon>0$, suppose the entry flow $f'$ is $2\varepsilon$-optimal, the current flow $f$ is $\varepsilon$-optimal, and each level $d(v)=(p(v)-p'(v))/\varepsilon$ is an integer. Suppose every excess has level at least $\lambda$ and every deficit has level zero. For $1\le i$ and $3i\le\lambda$, let $A_i\subseteq E^+$ contain the arcs whose tail has level in $\{3i,3i-1,3i-2\}$ and head has level in $\{3i-3,3i-4,3i-5\}$. Then
--
--   $$A_i\text{ meets every excess-to-deficit path in }G^+.$$
--
--   This supplies the cuts used in both cases of the excess estimate.
--
--   **Formalization Note** The proof prints “cut in $G_f$”; its argument uses Lemma 3 only on $E^+$, so the formal statement says $G^+$. Integer levels and zero level at deficits are explicit cost-scale invariants.
-- source:
--   Goldberg, Kaplan, Hed & Tarjan, Minimum Cost Flows in Graphs with Unit Capacities, STACS 2015 (LIPIcs 30), p. 410, proof of Lemma 5, second paragraph; https://doi.org/10.4230/LIPIcs.STACS.2015.406

import Mathlib
import Definitions.Def_UnitCapMCF_Excess_Setting

namespace UnitCapMCF.Excess

/-- Goldberg et al., STACS 2015, proof of Lemma 5, p. 410, second paragraph. -/
theorem lemma5_band_is_cut {V : Type*} [Fintype V] [DecidableEq V]
    (N : CostScaling.Refine.Network V) (ε : ℝ) (hε : 0 < ε)
    (f' f : V → V → ℝ) (p' p : V → ℝ)
    (hf' : CostScaling.Refine.IsEpsOptimal N (2 * ε) f' p')
    (hf : CostScaling.Refine.IsEpsOptimal N ε f p)
    (hd : ∀ v, ∃ k : ℤ, dlevel ε p' p v = k)
    (lam : ℕ)
    (hexc : ∀ v, 0 < CostScaling.Refine.excess N f v →
      (lam : ℝ) ≤ dlevel ε p' p v)
    (hdef : ∀ v, CostScaling.Refine.excess N f v < 0 →
      dlevel ε p' p v = 0)
    (i : ℕ) (hi : 1 ≤ i) (hile : 3 * i ≤ lam) :
    IsExcessDeficitCut N f' f (bandArcs N f' f ε p' p i) := by sorry

end UnitCapMCF.Excess
