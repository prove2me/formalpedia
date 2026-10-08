-- Prove2me | Theorems.Thm_PrimalDualLDR_FixedRecourse_proposition_2
-- name    : PrimalDualLDR.FixedRecourse.proposition_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T07:53:37.054961+00:00
-- url     : https://prove2.me/theorems/f82a5716-28de-4330-aa41-ebeca97d9036
-- title:
--   Proposition 2 — the moment matrix $M=\mathbb E(\xi\xi^\top)$ is positive definite and invertible
-- statement:
--   Assume the standing assumptions of §2; in particular the support $\Xi$ of $\mathbb P$ is bounded and spans $\mathbb R^k$. Then the second-order moment matrix
--   $$M = \mathbb E\big(\xi\xi^\top\big)$$
--   is positive definite and invertible.
--
--   Invertibility of $M$ lets the moment conditions $XM = \mathbb E(x(\xi)\xi^\top)$, $SM = \mathbb E(s(\xi)\xi^\top)$ of (2.5) determine $X$ and $S$ uniquely, and turns the constraint $AXM + SM - BM = 0$ of $\mathcal{SP}^l$ into $AX + S = B$.
--
--   **Formalization Note** Positive definiteness is Mathlib's `Matrix.PosDef` (symmetric with $v^\top M v > 0$ for $v \ne 0$); invertibility is `IsUnit M`. Both are stated, as printed, although the first implies the second.
-- source:
--   Kuhn, Wiesemann, Georghiou, Primal and dual linear decision rules in stochastic and robust optimization, Optimization Online 2009/02/2218, p. 7, Proposition 2

import Mathlib
import Definitions.Def_PrimalDualLDR_FixedRecourse_Basic
import Definitions.Def_PrimalDualLDR_FixedRecourse_Setting
import Definitions.Def_PrimalDualLDR_FixedRecourse_Problems

open MeasureTheory Matrix

namespace PrimalDualLDR.FixedRecourse

/-- Proposition 2 (p. 7): under the standing assumptions of §2, the second-order moment matrix
`M = E(ξξᵀ)` is positive definite and invertible. -/
theorem proposition_2 (σ : Setting) (hσ : σ.Standing) : σ.M.PosDef ∧ IsUnit σ.M := by sorry

end PrimalDualLDR.FixedRecourse
