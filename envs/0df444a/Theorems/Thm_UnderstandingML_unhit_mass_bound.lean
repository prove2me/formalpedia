-- Prove2me | Theorems.Thm_UnderstandingML_unhit_mass_bound
-- name    : UnderstandingML.unhit_mass_bound
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-24T04:56:04.673991+00:00
-- url     : https://prove2.me/theorems/b96e349e-8eef-48c7-b164-56da8916448a
-- title:
--   Lemma 19.2: for subsets C₁,…,C_r and an i.i.d. sample S of size m, E_S[∑_{i : Cᵢ ∩ S = ∅} P[Cᵢ]] ≤ r/(m e)
-- statement:
--   **Lemma 19.2.** Let $C_1, \dots, C_r$ be a collection of subsets of some domain set $X$. Let $S$ be a sequence of $m$ points sampled i.i.d. according to some probability distribution $D$ over $X$. Then
--   $$\mathbb{E}_{S \sim D^m}\Big[\sum_{i : C_i \cap S = \emptyset} P[C_i]\Big] \le \frac{r}{m e}.$$
--
--   Formally: the $C_i$ are measurable and $m \ge 1$.
-- source:
--   Shalev-Shwartz and Ben-David, Understanding Machine Learning: From Theory to Algorithms, Cambridge University Press 2014, doi:10.1017/CBO9781107298019, §19.2.1 p. 261, Lemma 19.2

import Definitions.Def_UnderstandingML_NearestNeighbor

open MeasureTheory

namespace UnderstandingML

open Classical in
/-- **Lemma 19.2** (p. 261). Let `C₁, …, C_r` be a collection of subsets of some domain set
`X`. Let `S` be a sequence of `m` points sampled i.i.d. according to some probability
distribution `D` over `X`. Then `E_{S ∼ D^m}[∑_{i : Cᵢ ∩ S = ∅} P[Cᵢ]] ≤ r / (m e)`.
The sets are measurable and `m ≥ 1`. -/
theorem unhit_mass_bound {X : Type*} [MeasurableSpace X] (D : Measure X) [IsProbabilityMeasure D]
    {r : ℕ} (C : Fin r → Set X) (hC : ∀ i, MeasurableSet (C i)) (m : ℕ) (hm : 0 < m) :
    ∫ S, ∑ i, (if ∀ j, S j ∉ C i then (D (C i)).toReal else 0) ∂(iidLaw D m) ≤
      r / (m * Real.exp 1) := by sorry

end UnderstandingML
