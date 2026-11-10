-- Prove2me | Theorems.Thm_SFLOracleLowerBound_Hardness_agreement_balanced
-- name    : SFLOracleLowerBound.Hardness.agreement_balanced
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T02:29:09.841009+00:00
-- url     : https://prove2.me/theorems/2722db40-09eb-48cc-a66c-18a712f9b0d9
-- title:
--   Lemma 14 — Agreement on balanced queries
-- statement:
--   In the replication of any symmetric assignment instance, take $R\ge1$, $\lambda>0$, and any valid hidden partition $\pi$. Every well-balanced query $T$ satisfies
--   $$g_\pi(T)=g_{\rm ref}(T).$$
--   Well-balanced means $|\xi_u(T)|\le\lambda$ for every base client $u$. This is the exact agreement property of the two computed oracle functions.
--
--   Differences from the source:
--   - encoding: public blocks B(i) of R|P_i| copies with hidden balanced labels → carrier C₀ × Fin R and all balanced labellings preserving each public orbit block; reason: the first coordinate indexes a public position and is not its hidden label; uniform balanced labellings give independent uniform partitions in the distinct blocks
-- source:
--   Adam N. Elmachtoub, Bento Natura, Meike Neuwohner, Settling the Approximability of Submodular Facility Location, STOC 2027 submission #1249 (October 2026), Lemma 14, p.13; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1249.pdf

import Mathlib
import Definitions.Def_SFLOracleLowerBound_Hardness_Replication

set_option autoImplicit false

noncomputable section

namespace SFLOracleLowerBound.Hardness

open Classical Finset MeasureTheory
open scoped ENNReal

/-- Lemma 14, p.13. -/

theorem agreement_balanced {C F : Type} [Fintype C] [Fintype F] [Nonempty C] [Nonempty F]
    [DecidableEq C] [DecidableEq F]
    (D : PublicData C F) (g : Finset C → ℝ) (Γ : Finset (Equiv.Perm C))
    (h : SymmetricInstance D g Γ) (R : ℕ) (hR : 0 < R) (lam : ℝ) (hlam : 0 < lam)
    (π : Copies C R → C) (hπ : HiddenPartition Γ R π) (T : Finset (Copies C R))
    (hT : WellBalanced Γ R lam π T) :
    hiddenCost Γ R lam g π T = referenceCost Γ R g T := by sorry

end SFLOracleLowerBound.Hardness
