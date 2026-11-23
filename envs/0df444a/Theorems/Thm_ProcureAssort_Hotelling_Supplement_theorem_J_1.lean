-- Prove2me | Theorems.Thm_ProcureAssort_Hotelling_Supplement_theorem_J_1
-- name    : ProcureAssort.Hotelling.Supplement.theorem_J_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T12:46:59.402396+00:00
-- url     : https://prove2.me/theorems/213ae611-556e-45c7-90e5-993577b9895a
-- title:
--   Theorem J.1 — Multiproduct scalar-type linear-pricing implementation
-- statement:
--   Fix any nonempty finite supplier set, arbitrary positive finite product counts, a valid quadratic consumer market on supplier-tagged products, and known product cost functions $c_{ip}(t)$. Suppose $h_i(x,t)=\sum_p c_{ip}(t)x_p$ has increasing differences on its stated real domain. There are thresholds $c^*\in\mathbb N$ and $d^*>0$ such that the following holds for independent finite positive scalar-type distributions with strictly increasing modified virtual costs.
--
--   Assume there is a profile $\theta$ at which every product is active, and every profile $\theta'$ with $\|\theta-\theta'\|_\infty\le d^*$ also has every product active. Assume $|\Theta_i|\ge c^*$ for every supplier and, for each adjacent supported pair $a<b$,
--
--   $$\max_{p\in P_i}\bigl(v_{ip}(b)-v_{ip}(a)\bigr)\le d^*/3.$$
--
--   Then $OPT(DecLin)=OPT(Cent)$ for mechanisms in which each supplier reports one scalar and IC and IR compare its total profit over all its products. Both feasible objective sets are nonempty and bounded above. This result keeps the product demand system unchanged while aggregating supplier transfers.
--
--   Differences from the source:
--
--   - reading: there exist c* and d* such that whenever the distributional conditions hold → thresholds are chosen after product and cost-function primitives and before the finite type laws; reason: the word whenever is read uniformly over those laws; allowing c* to depend on the realized support size would make the result vacuous by choosing it larger than every support
--   - reading: condition 1 re-introduces "a d* ∈ ℝ" after the outer d* ∈ ℝ+ that condition 2 uses → one positive d serves as the neighborhood radius of condition 1 and the gap threshold d/3 of condition 2; reason: the symbol is the same and Theorem 4.2 (p. 25), whose condition 1 J.1 copies, uses one d* in both conditions; a separate existential radius would be satisfied by radius 0 and empty the neighborhood clause
--   - encoding: a maximum over every product of a supplier → the bound holds for each product in its nonempty finite tagged product set; reason: a finite maximum is at most a number exactly when every entry is; reports remain supplier-level
--   - encoding: OPT denotes an actual optimal value → real suprema and nonempty bounded-above feasible objective sets with supplier-total IC, IR and transfers; reason: the product simplex is compact and costs are finite on finite type supports; interim IR bounds expected total transfers
-- source:
--   Saban & Weintraub, Procurement Mechanisms for Assortments of Differentiated Products, SSRN 3453144 (author version of 2020-03-03; Oper. Res. doi:10.1287/opre.2020.2053), Theorem J.1, p. 63

import Definitions.Def_ProcureAssort_Hotelling_Supplement_Multiproduct

namespace ProcureAssort.Hotelling.Supplement

theorem theorem_J_1 (n : ℕ) (hn : 0 < n) (m : Fin n → ℕ) (hm : ∀ i, 0 < m i)
    (M : QuadraticMarket (Product m)) (hM : M.Valid)
    (cost : (i : Fin n) → Fin (m i) → ℝ → ℝ)
    (hDiff : IncreasingCostDifferences m cost) :
    ∃ (c : ℕ) (d : ℝ), 0 < d ∧
      ∀ (Θ : Fin n → Finset ℝ) (f : Fin n → ℝ → ℝ), ValidTypes Θ f →
      (∀ i p, StrictMonoOn (multiVirtual m Θ f cost i p) (↑(Θ i) : Set ℝ)) →
        (∃ θ : Profile Θ, multiQ m Θ f M cost θ = Finset.univ ∧
          ∀ θ' : Profile Θ, TypeDistanceLE Θ θ θ' d →
            multiQ m Θ f M cost θ' = Finset.univ) →
      (∀ i, c ≤ (Θ i).card) →
      (∀ i, ∀ a b : ℝ, Consecutive (Θ i) a b →
        ∀ p : Fin (m i), multiVirtual m Θ f cost i p b - multiVirtual m Θ f cost i p a ≤ d/3) →
      sSup (multiDecValues m Θ f M cost) = sSup (multiCentValues m Θ f M cost) ∧
        (multiCentValues m Θ f M cost).Nonempty ∧ BddAbove (multiCentValues m Θ f M cost) ∧
        (multiDecValues m Θ f M cost).Nonempty ∧ BddAbove (multiDecValues m Θ f M cost) := by sorry

end ProcureAssort.Hotelling.Supplement
