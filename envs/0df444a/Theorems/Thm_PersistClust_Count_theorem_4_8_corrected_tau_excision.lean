-- Prove2me | Theorems.Thm_PersistClust_Count_theorem_4_8_corrected_tau_excision
-- name    : PersistClust.Count.theorem_4_8_corrected_tau_excision
-- status  : Proved
-- author  : @fabianroll
-- created : 2026-10-12T17:24:32.225993+00:00
-- url     : https://prove2.me/theorems/1a6b1e10-df16-41e5-b3a3-2787a61ed058
-- title:
--   Tau-excision: no sample vertex at tau kills all Rips bars born at tau with death at most 0
-- statement:
--   Let pts be a finite sample (n points) of a metric space X, let f be a real-valued function on X, and let tau > 0. Suppose no sample value equals tau (f (pts i) is different from tau for every index i). Then the Rips persistence diagram of the sample at any scale delta has multiplicity ZERO at every point born at tau whose death coordinate is at most 0 (this includes the essential case where the death coordinate is bottom). The reason: Rips persistence births are vertex values, and since the sample is finite, the values |f (pts i) - tau| have a positive minimum gamma; for every epsilon < gamma no vertex value lies in the window [tau - epsilon, tau + epsilon), so the stage sets at the two levels tau - epsilon and tau + epsilon coincide, and the rank functions entering the diagram's infimum formula agree at both levels. Every rank difference in that formula therefore collapses at such an epsilon, forcing the multiplicity to vanish. In the corrected Theorem 4.8 sample-count bound this is the tau-excision bridge: configurations whose diagram has a bar at (tau, d) with d at most 0 must contain a vertex with value exactly tau - a measure-zero event under the null hypothesis - so those configurations are negligible in the probability bound.
-- source:
--   The tau-excision bridge of theorem_4_8_corrected (id 6b9ad4c5-ed11-4695-b810-2a1269327d27, Open - the deliverable), Persistence-Based Clustering in Riemannian Manifolds (rr/6968): the shell2.md par.3 note - Rips births are vertex values, so no-vertex-at-tau forces the diagram to vanish at the tau-born low-death bars, feeding the negligibility of miscounted sample configurations. Companion of the accepted theorem_4_8_core (id 027bdb99) and of the accepted theorem_4_5 support cluster (elder_chase 9cfba490, essential_birth_gt_bound 652b6c32, separated_bar_death_lower_bound 819f90bb, born_component_subset abce3a62).

import Mathlib
import Definitions.Def_PersistClust_Count_Setting
import Definitions.Def_PersistClust_Count_Diagram
import Definitions.Def_PersistClust_Count_Rips

open PersistClust.Count

namespace PersistClust.Count

theorem theorem_4_8_corrected_tau_excision {X : Type*} [MetricSpace X] {n : ℕ} (f : X → ℝ) (τ : ℝ) (δ : ℝ)
    (pts : Fin n → X) (hτ : 0 < τ) (hne : ∀ i : Fin n, f (pts i) ≠ τ)
    (d : EReal) (hd : d ≤ ((0 : ℝ) : EReal)) :
    ripsDiagram (fun i j => dist (pts i) (pts j)) (f ∘ pts) δ (((τ : ℝ) : EReal), d) = 0
    := by sorry
