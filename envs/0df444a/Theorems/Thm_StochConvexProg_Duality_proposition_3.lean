-- Prove2me | Theorems.Thm_StochConvexProg_Duality_proposition_3
-- name    : StochConvexProg.Duality.proposition_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:16:57.136994+00:00
-- url     : https://prove2.me/theorems/48b07252-b889-472d-b899-5cde546deedb
-- title:
--   Proposition 3 — F is convex, not identically +∞, and lsc in the norm and in the weak topology of X × U
-- statement:
--   Under the standing assumptions, with $\sigma$ a probability measure, the functional $F:X\times U\to\mathbb R\cup\{+\infty\}$ is
--
--   1. convex (its epigraph is convex),
--   2. not identically $+\infty$, and
--   3. lower semicontinuous with respect to the normable (product norm) topology of $X\times U$, and also
--   4. lower semicontinuous with respect to the weak topology on $X\times U$ that is the product of the weak topology on $X$ induced by $V$ through (2.11) and the weak topology on $U$ induced by $Y$ through (1.6).
--
--   Proposition 3 is what allows the general perturbational duality theory to be applied to the problem $\mathbf P$ and its dual $\mathbf D$; its weak lower semicontinuity is the property used in the proof of Theorem 3.
--
--   **Formalization Note** The normable topology is Mathlib's product topology of the normed spaces $X$ and $U$; the weak topology is passed explicitly as a product of the two weak topologies. No boundedness of $C_1,C_2$ is assumed.
-- source:
--   Rockafellar and Wets, Stochastic convex programming: basic duality, Pacific J. Math. 62(1) (1976), p. 183, Proposition 3 (and the definition of the weak topology just before it)

import Mathlib
import Definitions.Def_StochConvexProg_Duality_Problem
import Definitions.Def_StochConvexProg_Duality_Dual

open MeasureTheory

namespace StochConvexProg.Duality

/-- Rockafellar–Wets (1976), p. 183, Proposition 3: `F` on `X × U` is convex, not identically
`+∞`, and lower semicontinuous both for the normable topology and for the weak topology on
`X × U` induced by the pairing with `V × Y` (product of the weak topologies of (2.11) and (1.6)). -/
theorem proposition_3 {S : Type*} [MeasurableSpace S] {σ : Measure S}
    [IsProbabilityMeasure σ] {n₁ n₂ m₁ m₂ : ℕ} (pr : Problem S σ n₁ n₂ m₁ m₂) :
    EConvex (fun p : XSpace σ n₁ n₂ × USpace σ m₁ m₂ => pr.F p.1 p.2) ∧
      (∃ p : XSpace σ n₁ n₂ × USpace σ m₁ m₂, pr.F p.1 p.2 ≠ ⊤) ∧
      LowerSemicontinuous (fun p : XSpace σ n₁ n₂ × USpace σ m₁ m₂ => pr.F p.1 p.2) ∧
      @LowerSemicontinuous (XSpace σ n₁ n₂ × USpace σ m₁ m₂) EReal
        (@instTopologicalSpaceProd _ _ (weakX σ n₁ n₂) (weakU σ m₁ m₂)) _
        (fun p : XSpace σ n₁ n₂ × USpace σ m₁ m₂ => pr.F p.1 p.2) := by sorry

end StochConvexProg.Duality
