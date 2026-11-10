-- Prove2me | Theorems.Thm_SFLOracleLowerBound_Hardness_replicated_optima
-- name    : SFLOracleLowerBound.Hardness.replicated_optima
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T02:29:09.41439+00:00
-- url     : https://prove2.me/theorems/a311e717-7858-48c8-8ccc-3028d7a1481c
-- title:
--   Lemma 13 — Replicated optima
-- statement:
--   Fix the symmetric base instance, a positive replication factor $R$, a penalty $\lambda>0$ and a valid hidden partition. With the actual allocation optima of the base, reference and hidden instances,
--   $$\mathrm{OPT}_{\rm ref}=R\mathrm{OPT}_{\rm sym},\qquad \mathrm{OPT}_\pi\le R\mathrm{OPT}_0+\lambda|\mathcal C_0|.$$
--   The equalities and inequalities also retain the general allocation model's infinite values. They relate the constructed optima to the source symmetry gap.
--
--   Differences from the source:
--   - encoding: public blocks B(i) of R|P_i| copies with hidden balanced labels → carrier C₀ × Fin R and all balanced labellings preserving each public orbit block; reason: the first coordinate indexes a public position and is not its hidden label; uniform balanced labellings give independent uniform partitions in the distinct blocks
--   - encoding: nonnegative allocation costs, possibly +∞ → ENNReal costs and an infimum over feasible assignments; reason: there are finitely many assignments, so each nonempty feasible family attains its minimum; the empty feasible family has value +∞
-- source:
--   Adam N. Elmachtoub, Bento Natura, Meike Neuwohner, Settling the Approximability of Submodular Facility Location, STOC 2027 submission #1249 (October 2026), Lemma 13(i)–(ii), p.11; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1249.pdf

import Mathlib
import Definitions.Def_SFLOracleLowerBound_Hardness_Replication

set_option autoImplicit false

noncomputable section

namespace SFLOracleLowerBound.Hardness

open Classical Finset MeasureTheory
open scoped ENNReal

/-- Lemma 13(i)–(ii), p.11. -/

theorem replicated_optima {C F : Type} [Fintype C] [Fintype F] [Nonempty C] [Nonempty F]
    [DecidableEq C] [DecidableEq F]
    (D : PublicData C F) (g : Finset C → ℝ) (Γ : Finset (Equiv.Perm C))
    (h : SymmetricInstance D g Γ) (R : ℕ) (hR : 0 < R) (lam : ℝ) (hlam : 0 < lam)
    (π : Copies C R → C) (hπ : HiddenPartition Γ R π) :
    optimum (replicatedData D R) (referenceCost Γ R g) = (R : ℝ≥0∞) * symmetricOptimum D g Γ ∧
    optimum (replicatedData D R) (hiddenCost Γ R lam g π) ≤
      (R : ℝ≥0∞) * optimum D g + ENNReal.ofReal (lam * Fintype.card C) := by sorry

end SFLOracleLowerBound.Hardness
