-- Prove2me | Theorems.Thm_StochKolmogorov_Classify_sink_box_avoids_far_set
-- name    : StochKolmogorov.Classify.sink_box_avoids_far_set
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-11-03T18:23:20.768861+00:00
-- url     : https://prove2.me/theorems/6c89bdad-fa68-4d81-b04a-1e6033e2466d
-- title:
--   Started near an extinction measure $\mu\in\mathcal M^1$, the solution avoids every far set $\{\|y\|_1<R,\ y_i>\eta,\ i\notin\operatorname{supp}\mu\}$ forever with probability $>1-\varepsilon$
-- statement:
--   Under Assumption 1.1, let $\mu\in\mathcal M^1$, $k\ge1$, $\varepsilon>0$, $R\in\mathbb R$ and $\eta>0$. Then there is $\Delta>0$ such that for every $x\in\mathcal K^{k,\Delta}_\mu$,
--
--   $$\mathbb P\Big(\forall t\ge0:\ \neg\big(\|X^x(t)\|_1<R\ \text{and}\ X^x_i(t)>\eta\ \text{for some } i\notin\operatorname{supp}\mu\big)\Big)>1-\varepsilon .$$
--
--   Role: this is the probabilistic core (5.27)-(5.33) of Lemma 5.9: the function $\tilde U$ is a supermartingale along a time grid, so by a Doob-type bound the non-sink coordinates stay small at all grid times, and short-time positivity then rules out excursions into the far set between grid times; afterwards every weak limit of occupation measures puts no mass on the far set.
-- source:
--   A. Hening, D. H. Nguyen, Coexistence and extinction for stochastic Kolmogorov systems, Ann. Appl. Probab. 28 (2018), https://arxiv.org/abs/1704.06984v1, proof of Lemma 5.9, pp. 26-27, displays (5.27)-(5.33) (supermartingale property of tilde U from Proposition 5.1 and (5.11)-(5.12), Doob's inequality on the grid, and (5.19))

import Mathlib
import Definitions.Def_StochKolmogorov_Classify_Model
import Definitions.Def_StochKolmogorov_Classify_Faces
import Definitions.Def_StochKolmogorov_Classify_Classification
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace StochKolmogorov.Classify

open EthierKurtz

theorem sink_box_avoids_far_set {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (C : Coeffs n)
    (B : ℝ≥0 → Ω → SDEState n) (X : SDEState n → ℝ≥0 → Ω → SDEState n)
    (hX : IsSolutionFamily P C B X) (c : SDEState n) (γb : ℝ) (hA : Assumption11 C c γb) :
    ∀ μ ∈ M1 P C X, ∀ k : ℕ, 1 ≤ k → ∀ ε : ℝ, 0 < ε → ∀ R η : ℝ, 0 < η →
      ∃ Δ : ℝ, 0 < Δ ∧ ∀ x ∈ Kbox μ k Δ, 1 - ε < (P {ω | ∀ t : ℝ≥0,
        ¬ (l1 (X x t ω) < R ∧ ∃ i, i ∉ supp μ ∧ η < X x t ω i)}).toReal := by sorry

end StochKolmogorov.Classify
