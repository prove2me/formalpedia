-- Prove2me | Theorems.Thm_SFLOracleLowerBound_Hardness_replicated_instances
-- name    : SFLOracleLowerBound.Hardness.replicated_instances
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T02:29:03.091693+00:00
-- url     : https://prove2.me/theorems/35517e38-31f9-4741-81fc-81e7c7812331
-- title:
--   Lemma 12 — Replicated instances
-- statement:
--   Fix a symmetric assignment instance, $R\ge1$, $\lambda>0$ and a valid hidden partition $\pi$. Both $g_\pi$ and $g_{\rm ref}$ are normalized, monotone and submodular. Moreover,
--   $$Rg\text{ integer-valued}\ \Longrightarrow\ g_{\rm ref}\text{ is a matroid rank function},$$
--   and if also $\lambda$ is an integer, $g_\pi$ is a matroid rank function. The reference cost is independent of the hidden partition and
--   $$g_\pi(T)\le g_{\rm ref}(T)\qquad(T\subseteq\mathcal C).$$
--   These properties establish that the computed hidden and reference functions are valid facility costs. Independence is expressed by equality of the restricted-witness formula through any valid partition with the public formula.
--
--   Differences from the source:
--   - encoding: public blocks B(i) of R|P_i| copies with hidden balanced labels → carrier C₀ × Fin R and all balanced labellings preserving each public orbit block; reason: the first coordinate indexes a public position and is not its hidden label; uniform balanced labellings give independent uniform partitions in the distinct blocks
-- source:
--   Adam N. Elmachtoub, Bento Natura, Meike Neuwohner, Settling the Approximability of Submodular Facility Location, STOC 2027 submission #1249 (October 2026), Lemma 12(i)–(iii), p.11; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1249.pdf

import Mathlib
import Definitions.Def_SFLOracleLowerBound_Hardness_Replication

set_option autoImplicit false

noncomputable section

namespace SFLOracleLowerBound.Hardness

open Classical Finset MeasureTheory
open scoped ENNReal

/-- Lemma 12(i)–(iii), p.11. -/

theorem replicated_instances {C F : Type} [Fintype C] [Fintype F] [Nonempty C] [Nonempty F]
    [DecidableEq C] [DecidableEq F]
    (D : PublicData C F) (g : Finset C → ℝ) (Γ : Finset (Equiv.Perm C))
    (h : SymmetricInstance D g Γ) (R : ℕ) (hR : 0 < R) (lam : ℝ) (hlam : 0 < lam)
    (π : Copies C R → C) (hπ : HiddenPartition Γ R π) :
    (FacilityCost (hiddenCost Γ R lam g π) ∧ FacilityCost (referenceCost Γ R g)) ∧
    (IntegerValued (fun S => (R : ℝ) * g S) →
      MatroidRank (referenceCost Γ R g) ∧
      ((∃ z : ℤ, lam = z) → MatroidRank (hiddenCost Γ R lam g π))) ∧
    (∀ T, referenceViaPartition Γ R g π T = referenceCost Γ R g T) ∧
    (∀ T, hiddenCost Γ R lam g π T ≤ referenceCost Γ R g T) := by sorry

end SFLOracleLowerBound.Hardness
