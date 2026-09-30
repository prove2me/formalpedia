-- Prove2me | Theorems.Thm_Wets1974_Feasibility_K2_eq_iInter_of_closedPosHull_eq
-- name    : Wets1974.Feasibility.K2_eq_iInter_of_closedPosHull_eq
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-29T14:32:34.241496+00:00
-- url     : https://prove2.me/theorems/87198184-7f8e-41bc-b686-4ba66fae51f2
-- title:
--   Theorem 4.6 — $K_2 = \bigcap_{\zeta \in \Sigma} K_2(\zeta)$ for every $\Sigma$ with the same closed positive hull as $\tilde\Xi_{p,T}$
-- statement:
--   Let $W$ be a fixed $\bar m \times \bar n$ matrix, $\mu$ the law of $\xi = (c, q, p, T)$, $\tilde\Xi_{p,T}$ the support of the marginal law of $(p, T)$, and $K_2 = \bigcap_{\zeta \in \tilde\Xi_{p,T}} K_2(\zeta)$ with $K_2(\zeta) = \{x \mid p - Tx \in \operatorname{pos} W\}$ for $\zeta = (p,T)$. For a set $S$ of $(p,T)$-space write $\operatorname{pos}(S)$ for its closed positive hull, the closure of the set of nonnegative linear combinations of points of $S$.
--
--   If $\Sigma$ is any set of $(p,T)$-space with $\operatorname{pos}(\Sigma) = \operatorname{pos}(\tilde\Xi_{p,T})$, then
--
--   $$
--   K_2 = \bigcap_{\zeta \in \Sigma} K_2(\zeta).
--   $$
--
--   The theorem allows the support in the definition of $K_2$ to be replaced by any set generating the same closed cone: its closure, its convex hull, its positive hull, positive multiples of its points, a dense subset, a generating set, or the extreme points of a compact support. The paper uses it with $\Sigma$ the closed convex hull of the support in the proof of Theorem 4.10.
--
--   **Formalization Note.** The paper states the theorem for "a set obtained from $\tilde\Xi_{p,T}$ by applying the operations: topological closure, convex closure, positive closure, positive scalar multiplication or any of the (not necessarily unique) inverses of these operations", with the inverse of convex closure yielding the extreme points. Read literally this is false: if $\tilde\Xi_{p,T}$ is a closed half-plane it has no extreme points, so $\Sigma = \emptyset$ and $\bigcap_{\zeta \in \emptyset} K_2(\zeta) = \mathbb{R}^n \ne K_2$ in general. This statement is the reading the paper's proof supports ("pos $W$ is closed … pos $W$ is a convex cone"): every such operation, and every inverse that preserves the closed positive hull, is covered.
-- source:
--   Wets, Stochastic Programs with Fixed Recourse: The Equivalent Deterministic Program, SIAM Review 16(3), 1974, pp. 316-317, Theorem 4.6 (corrected reading: same closed positive hull)

import Mathlib
import Definitions.Def_Wets1974_Feasibility_Model

namespace Wets1974.Feasibility

open MeasureTheory

/-- Theorem 4.6, pp. 316-317, in the reading its proof supports: for every set `Σ` of
`(p, T)`-space whose closed positive hull equals that of `Ξ̃_{p,T}`,
`K₂ = ⋂_{ζ ∈ Σ} K₂(ζ)`. -/
theorem K2_eq_iInter_of_closedPosHull_eq {n nb mb : ℕ} (μ : Measure (DataSpace n nb mb))
    [IsProbabilityMeasure μ] (W : Matrix (Fin mb) (Fin nb) ℝ)
    (Sig : Set (PTSpace n mb)) (hSig : closedPosHull Sig = closedPosHull (suppPT μ)) :
    K2 μ W = ⋂ ζ ∈ Sig, K2of W ζ := by sorry

end Wets1974.Feasibility
