-- Prove2me | Theorems.Thm_PolymerEndpoint_Atomic_lemma_6_2
-- name    : PolymerEndpoint.Atomic.lemma_6_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T03:36:44.170955+00:00
-- url     : https://prove2.me/theorems/512ff45d-8717-4267-87c4-3f767bb1a3f5
-- title:
--   Lemma 6.2 — sufficient condition for pure atomicity
-- statement:
--   Suppose that for every real $c<1$ there is a threshold $\varepsilon>0$ such that the lower limit of the Cesàro mean of endpoint mass above that fixed threshold exceeds $c$ almost surely:
--   $$
--   \liminf_{n\to\infty}\frac1n\sum_{i=0}^{n-1}
--   \rho_i(\omega_i\in\mathcal A_i^\varepsilon)>c\quad\text{a.s.}
--   $$
--   Then the endpoint distributions are asymptotically purely atomic for every positive threshold sequence tending to zero.
--
--   This reduces the varying-threshold conclusion to fixed-threshold lower bounds.
-- source:
--   Bates and Chatterjee, The endpoint distribution of directed polymers, arXiv:1612.03443v5, p. 43, Lemma 6.2

import Definitions.Def_PolymerEndpoint_Atomic_Functionals

open MeasureTheory Filter Finset
open scoped BigOperators Topology

namespace PolymerEndpoint.Atomic

theorem lemma_6_2 {d : ℕ} (hd : 1 ≤ d) {Ω : Type*} [MeasurableSpace Ω]
    (X : Cell d → Ω → ℝ) (β : ℝ) (P : Measure Ω)
    (h : ∀ c : ℝ, c < 1 → ∃ ε : ℝ, 0 < ε ∧
      ∀ᵐ a ∂P, c < Filter.liminf
        (fun n : ℕ => (n : ℝ)⁻¹ *
          ∑ i ∈ Finset.range n, atomMass X β i ε a) atTop) :
    AsympPurelyAtomic X β P := by sorry

end PolymerEndpoint.Atomic
