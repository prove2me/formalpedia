-- Prove2me | Theorems.Thm_SymmetricDepthHierarchy_ConstantDepth_nonrich_class_closure
-- name    : SymmetricDepthHierarchy.ConstantDepth.nonrich_class_closure
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T04:32:31.494983+00:00
-- url     : https://prove2.me/theorems/d8bee497-58ca-4efd-b8bb-53063b17bad4
-- title:
--   Corollary B.18: the non-$(\Delta,k)$-rich graphs contain $K_1$ and are closed under minors and weak oddomorphisms
-- statement:
--   Let $\Delta,k\ge1$ and let $\mathcal F$ be the class of all finite graphs that are not $(\Delta,k)$-rich. Then
--
--   1. $K_1\in\mathcal F$,
--   2. $\mathcal F$ is closed under taking minors, and
--   3. $\mathcal F$ is closed under weak oddomorphisms.
--
--   These are exactly the hypotheses of Theorem 3.7 for this class.
--
--   Differences from the source:
--   - encoding: a class of simple graphs → a set of FinGraph (finite vertex type in Type with a simple graph); reason: classes here are minor-closed or defined by an isomorphism-invariant predicate, so membership does not depend on the encoding
-- source:
--   Anuj Dawar, Prateek Dwivedi, Benedikt Pago, Tim Seppelt, STOC 2027 submission #1521 (October 2026), p. 36 (PDF p. 39), Corollary B.18

import Mathlib
import Definitions.Def_SymmetricDepthHierarchy_ConstantDepth_Pattern
import Definitions.Def_SymmetricDepthHierarchy_ConstantDepth_Richness
import Definitions.Def_SymmetricDepthHierarchy_ConstantDepth_Oddomorphism

open scoped Classical

namespace SymmetricDepthHierarchy.ConstantDepth

/-- Corollary B.18, printed p. 36 (PDF p. 39). Let `Δ, k ≥ 1`. The class `𝓕` of all graphs that are
not `(Δ, k)`-rich contains `K₁` and is closed under taking minors and weak oddomorphisms. -/
theorem nonrich_class_closure (Δ k : ℕ) (hΔ : 1 ≤ Δ) (hk : 1 ≤ k) :
    K1 ∈ {X : FinGraph | ¬ Rich Δ k X.G} ∧
      MinorClosed {X : FinGraph | ¬ Rich Δ k X.G} ∧
      WeakOddClosed {X : FinGraph | ¬ Rich Δ k X.G} := by sorry

end SymmetricDepthHierarchy.ConstantDepth
