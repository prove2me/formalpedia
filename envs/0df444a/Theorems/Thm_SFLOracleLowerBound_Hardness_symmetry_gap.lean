-- Prove2me | Theorems.Thm_SFLOracleLowerBound_Hardness_symmetry_gap
-- name    : SFLOracleLowerBound.Hardness.symmetry_gap
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T02:29:00.216362+00:00
-- url     : https://prove2.me/theorems/08a0e24e-3b3b-4abe-beac-bc971076794c
-- title:
--   Theorem 10 — Symmetry-gap theorem
-- statement:
--   Let $(\mathcal C_0,\mathcal F,D,g,\Gamma)$ be a symmetric assignment instance, including $g(P_i)\le|P_i|$ on each orbit. Suppose $\alpha\ge1$, $\nu>0$, and
--   $$\alpha(\mathrm{OPT}_0+\nu)<\mathrm{OPT}_{\rm sym}.$$
--   For every positive integer $R$, use the hidden-instance family with $R$ copies per base client and $\lambda=R\nu/|\mathcal C_0|$. All its costs are valid. For every randomized algorithm using at most $Q$ queries on every run, some family member has approximation-success probability at most
--   $$2(Q+|\mathcal F|)|\mathcal C_0|\exp\left(-\frac{2R\nu^2}{|\mathcal C_0|^2}\right).$$
--   If $Rg$ is integer-valued and $R\nu/|\mathcal C_0|$ is an integer, every facility cost in the family is a matroid rank function. Public connection costs may be infinite and oracle answers may be arbitrary nonnegative reals.
--
--   The result converts a symmetric allocation instance with the stated strict gap into a quantitative value-oracle lower bound. The output's facility clusters are accounted for by the term $|\mathcal F|$.
--
--   Differences from the source:
--   - encoding: public blocks B(i) of R|P_i| copies with hidden balanced labels → carrier C₀ × Fin R and all balanced labellings preserving each public orbit block; reason: the first coordinate indexes a public position and is not its hidden label; uniform balanced labellings give independent uniform partitions in the distinct blocks
--   - encoding: nonnegative allocation costs, possibly +∞ → ENNReal costs and an infimum over feasible assignments; reason: there are finitely many assignments, so each nonempty feasible family attains its minimum; the empty feasible family has value +∞
--   - encoding: arbitrary adaptive randomized exact-value algorithms → transcript strategies with real answers and private seeds on arbitrary probability spaces, with measurable observable runs; reason: all oracle dependence occurs through the transcript; measurability makes the stated probabilities well-defined and no support restriction is imposed
-- source:
--   Adam N. Elmachtoub, Bento Natura, Meike Neuwohner, Settling the Approximability of Submodular Facility Location, STOC 2027 submission #1249 (October 2026), Theorem 10, pp.9–10; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1249.pdf

import Mathlib
import Definitions.Def_SFLOracleLowerBound_Hardness_Replication

set_option autoImplicit false

noncomputable section

namespace SFLOracleLowerBound.Hardness

open Classical Finset MeasureTheory
open scoped ENNReal

/-- Theorem 10, pp.9–10. Exact slack α(OPT₀+ν) and output-cluster term |ℱ|. -/

theorem symmetry_gap {C F : Type} [Fintype C] [Fintype F] [Nonempty C] [Nonempty F]
    [DecidableEq C] [DecidableEq F]
    (D : PublicData C F) (g : Finset C → ℝ) (Γ : Finset (Equiv.Perm C))
    (h : SymmetricInstance D g Γ) (α nu : ℝ) (hα : 1 ≤ α) (hnu : 0 < nu)
    (hgap : ENNReal.ofReal α * (optimum D g + ENNReal.ofReal nu) < symmetricOptimum D g Γ)
    (R : ℕ) (hR : 0 < R) :
    (partitions Γ R).Nonempty ∧
    (∀ π, HiddenPartition Γ R π →
      FacilityCost (hiddenCost Γ R ((R : ℝ)*nu/Fintype.card C) g π) ∧
      (IntegerValued (fun S => (R : ℝ)*g S) →
       (∃ z : ℤ, (R : ℝ)*nu/Fintype.card C = z) →
       MatroidRank (hiddenCost Γ R ((R : ℝ)*nu/Fintype.card C) g π))) ∧
    ∀ (A : RandomAlgorithm (Copies C R) F) (Q : ℕ),
      (∀ k : Finset (Copies C R) → ℝ, FacilityCost k → WithinBudget A k Q) →
      ∃ π, HiddenPartition Γ R π ∧
        successProbability A (replicatedData D R)
          (hiddenCost Γ R ((R : ℝ)*nu/Fintype.card C) g π) Q α ≤
        2 * (Q + Fintype.card F) * Fintype.card C *
          Real.exp (-2 * R * nu^2 / (Fintype.card C : ℝ)^2) := by sorry

end SFLOracleLowerBound.Hardness
