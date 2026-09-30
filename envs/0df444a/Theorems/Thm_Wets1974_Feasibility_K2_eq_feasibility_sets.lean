-- Prove2me | Theorems.Thm_Wets1974_Feasibility_K2_eq_feasibility_sets
-- name    : Wets1974.Feasibility.K2_eq_feasibility_sets
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-29T14:32:10.3211+00:00
-- url     : https://prove2.me/theorems/b9377002-1b1d-4984-896f-6455f17b27a3
-- title:
--   Corollary 4.5 — $K_2 = K_2^p = K_2^\mu = K_2^s$ with $K_2$ over the support of $(p,T)$
-- statement:
--   In the setting of Theorem 4.1 (fixed recourse matrix $W$ of size $\bar m \times \bar n$, random data $\xi = (c, q, p, T)$ with law $\mu$), let $\tilde\Xi_{p,T}$ be the support of the marginal distribution of $(p(\xi), T(\xi))$ and, for $\zeta = (p, T)$, let $K_2(\zeta) = \{x \mid p - Tx \in \operatorname{pos} W\}$, where $\operatorname{pos} W = \{Wy \mid y \ge 0\}$. Put
--
--   $$
--   K_2 = \bigcap_{\zeta \in \tilde\Xi_{p,T}} K_2(\zeta) = \{x \mid p - Tx \in \operatorname{pos} W \text{ for all } (p, T) \in \tilde\Xi_{p,T}\}.
--   $$
--
--   If $\xi$ satisfies the weak covariance condition (Definition 2.2) and $W$ has full row rank, then
--
--   $$
--   K_2 = K_2^p = K_2^\mu = K_2^s,
--   $$
--
--   with $K_2^p$, $K_2^\mu$, $K_2^s$ as in Theorem 4.1.
--
--   The new content over Theorem 4.1 is that the support of the $(p,T)$-marginal may replace the support of $\xi$: feasibility depends only on the right-hand side and technology matrix. From here on the paper writes $K_2$ for this common set.
--
--   **Formalization Note.** $\tilde\Xi_{p,T}$ is the support of the pushforward of $\mu$ under the coordinate projection $\xi \mapsto (p, T)$, which is continuous and hence measurable. Full row rank of $W$ is the paper's standing assumption (p. 312).
-- source:
--   Wets, Stochastic Programs with Fixed Recourse: The Equivalent Deterministic Program, SIAM Review 16(3), 1974, p. 316, Corollary 4.5 (with Eq. (4.4))

import Mathlib
import Definitions.Def_Wets1974_Feasibility_Model

namespace Wets1974.Feasibility

open MeasureTheory

/-- Corollary 4.5, p. 316: under the weak covariance condition (Definition 2.2) and the
standing assumption that `W` has full row rank (p. 312), `K₂ = K₂^p = K₂^μ = K₂^s`, where
`K₂ = ⋂_{ζ ∈ Ξ̃_{p,T}} K₂(ζ)`. -/
theorem K2_eq_feasibility_sets {n nb mb : ℕ} (μ : Measure (DataSpace n nb mb))
    [IsProbabilityMeasure μ] (W : Matrix (Fin mb) (Fin nb) ℝ)
    (hW : W.rank = mb) (hcov : WeakCovariance μ) :
    K2 μ W = K2supp μ W ∧ K2supp μ W = K2mu μ W ∧ K2mu μ W = K2s μ W := by sorry

end Wets1974.Feasibility
