-- Prove2me | Theorems.Thm_SFLOracleLowerBound_Hardness_agreement_fixed_query
-- name    : SFLOracleLowerBound.Hardness.agreement_fixed_query
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T02:28:52.188073+00:00
-- url     : https://prove2.me/theorems/c06b413c-aa4b-465e-92d5-45f243393368
-- title:
--   Lemma 17 — Agreement on a fixed query
-- statement:
--   Fix a query $T$ in the replication with $R\ge1$ and $\lambda>0$, and draw $\pi$ uniformly and independently inside the public blocks, with exactly $R$ copies of every base label. Then
--   $$\Pr_\pi[g_\pi(T)\ne g_{\rm ref}(T)]\le\Pr_\pi[T\text{ is not well-balanced}]\le2|\mathcal C_0|\exp(-2\lambda^2/R).$$
--   The probability is over the hidden partition, with the query fixed. This is the quantitative agreement estimate for the replication family.
--
--   Differences from the source:
--   - encoding: public blocks B(i) of R|P_i| copies with hidden balanced labels → carrier C₀ × Fin R and all balanced labellings preserving each public orbit block; reason: the first coordinate indexes a public position and is not its hidden label; uniform balanced labellings give independent uniform partitions in the distinct blocks
-- source:
--   Adam N. Elmachtoub, Bento Natura, Meike Neuwohner, Settling the Approximability of Submodular Facility Location, STOC 2027 submission #1249 (October 2026), Lemma 17, p.14; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1249.pdf

import Mathlib
import Definitions.Def_SFLOracleLowerBound_Hardness_Replication

set_option autoImplicit false

noncomputable section

namespace SFLOracleLowerBound.Hardness

open Classical Finset MeasureTheory
open scoped ENNReal

/-- Lemma 17, p.14. Uniform balanced block labellings, not independent sampling. -/

theorem agreement_fixed_query {C F : Type} [Fintype C] [Fintype F] [Nonempty C] [Nonempty F]
    [DecidableEq C] [DecidableEq F]
    (D : PublicData C F) (g : Finset C → ℝ) (Γ : Finset (Equiv.Perm C))
    (h : SymmetricInstance D g Γ) (R : ℕ) (hR : 0 < R) (lam : ℝ) (hlam : 0 < lam)
    (T : Finset (Copies C R)) :
    partitionProbability Γ R (fun π => hiddenCost Γ R lam g π T ≠ referenceCost Γ R g T) ≤
      partitionProbability Γ R (fun π => ¬ WellBalanced Γ R lam π T) ∧
    partitionProbability Γ R (fun π => ¬ WellBalanced Γ R lam π T) ≤
      2 * Fintype.card C * Real.exp (-2 * lam^2 / R) := by sorry

end SFLOracleLowerBound.Hardness
