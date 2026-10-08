-- Prove2me | Theorems.Thm_PrimalDualLDR_FixedRecourse_sec_2_2_constraints
-- name    : PrimalDualLDR.FixedRecourse.sec_2_2_constraints
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T07:53:32.048715+00:00
-- url     : https://prove2.me/theorems/c439a507-47e1-4170-8d2f-157fbb4d5f07
-- title:
--   §2.2, p. 5 — the a.s. constraints of $\mathcal{SP}^u$ hold on all of $\Xi$, and $AX\xi+S\xi=B\xi$ a.s. iff $AX+S=B$
-- statement:
--   Assume the standing assumptions of §2: $\Xi = \{W\xi \ge h\}$ is the support of $\mathbb P$, nonempty and bounded, of the form (2.1b), and spans $\mathbb R^k$. Let $X \in \mathbb R^{n\times k}$ and $S \in \mathbb R^{m\times k}$. Then
--
--   1. $AX\xi + S\xi = B\xi$ holds for $\mathbb P$-almost every $\xi$ if and only if it holds for every $\xi \in \Xi$;
--   2. $S\xi \ge 0$ holds for $\mathbb P$-almost every $\xi$ if and only if it holds for every $\xi \in \Xi$;
--   3. $AX\xi + S\xi = B\xi$ holds for $\mathbb P$-almost every $\xi$ if and only if
--   $$AX + S = B.$$
--
--   The first two items say that the almost-sure constraints of $\mathcal{SP}^u$ are robust constraints over the support $\Xi$; the third replaces the semi-infinite equality constraint by a finite matrix equation. Together with Proposition 1 they turn $\mathcal{SP}^u$ into the linear program (2.3).
-- source:
--   Kuhn, Wiesemann, Georghiou, Primal and dual linear decision rules in stochastic and robust optimization, Optimization Online 2009/02/2218, §2.2, p. 5 (unnumbered claim)

import Mathlib
import Definitions.Def_PrimalDualLDR_FixedRecourse_Basic
import Definitions.Def_PrimalDualLDR_FixedRecourse_Setting
import Definitions.Def_PrimalDualLDR_FixedRecourse_Problems

open MeasureTheory Matrix

namespace PrimalDualLDR.FixedRecourse

/-- §2.2, p. 5 (unnumbered): under the standing assumptions of §2, the almost-sure constraints of
`SP^u` hold for every `ξ` in the support `Ξ`, and the almost-sure equality constraint
`AXξ + Sξ = Bξ` is equivalent to the matrix equation `AX + S = B`. -/
theorem sec_2_2_constraints (σ : Setting) (hσ : σ.Standing)
    (X : Matrix (Fin σ.n) (Fin σ.k) ℝ) (S : Matrix (Fin σ.m) (Fin σ.k) ℝ) :
    ((∀ᵐ ξ ∂σ.P, σ.A.mulVec (X.mulVec ξ) + S.mulVec ξ = σ.B.mulVec ξ) ↔
        ∀ ξ ∈ σ.Xi, σ.A.mulVec (X.mulVec ξ) + S.mulVec ξ = σ.B.mulVec ξ) ∧
    ((∀ᵐ ξ ∂σ.P, ∀ i, 0 ≤ (S.mulVec ξ) i) ↔ ∀ ξ ∈ σ.Xi, ∀ i, 0 ≤ (S.mulVec ξ) i) ∧
    ((∀ᵐ ξ ∂σ.P, σ.A.mulVec (X.mulVec ξ) + S.mulVec ξ = σ.B.mulVec ξ) ↔ σ.A * X + S = σ.B) := by sorry

end PrimalDualLDR.FixedRecourse
