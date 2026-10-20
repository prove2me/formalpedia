-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P35_divergence_limits
-- name    : QAlgorithms.Papers.Independent.Dependency50.P35.divergence_limits
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T14:54:13.062535+00:00
-- url     : https://prove2.me/theorems/9ca4db07-721b-435a-a91c-fd7250d83a36
-- title:
--   Theorem 5: limits to relative entropy and max-relative entropy
-- statement:
--   Let $\rho,\sigma\ge0$ be finite-dimensional operators, with $\rho\ne0$ and $\ker\sigma\subseteq\ker\rho$. Write $D_1(\rho\|\sigma)=\operatorname{Tr}[\rho(\log_2\rho-\log_2\sigma)]/\operatorname{Tr}\rho$ and $D_{\max}(\rho\|\sigma)=\inf\{\lambda\in\mathbb R:\rho\le2^\lambda\sigma\}$. Then
--
--   $$
--   \lim_{\alpha\to\infty}\widetilde D_\alpha(\rho\|\sigma)=D_{\max}(\rho\|\sigma),\qquad
--   \lim_{\alpha\uparrow1}\widetilde D_\alpha(\rho\|\sigma)=D_1(\rho\|\sigma)=\lim_{\alpha\downarrow1}\widetilde D_\alpha(\rho\|\sigma).
--   $$
--
--   No trace normalization of the arguments is required. These are the three limiting-case identifications of Theorem 5.
-- source:
--   On quantum Renyi entropies: a new generalization and some properties, arXiv:1306.3142v4, PDF p. 8, Theorem 5

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P35

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder ENNReal

open Filter Topology

namespace QAlgorithms.Papers.Independent.Dependency50.P35

attribute [local instance] Classical.propDecidable Classical.decEq

-- Reuse the accepted matrix type and positive-operator Schatten expression.

open QAlgorithms.Papers.Independent.Information100.P63 (Mat schatten)

open QAlgorithms.Papers.Independent.Information100.P58 (Distribution)

/-- PDF p.8, Theorem 5: both one-sided limits at one and the limit at infinity. -/
theorem divergence_limits {I : Type} [Fintype I] [DecidableEq I]
    (rho sigma : Mat I) (hr : rho.PosSemidef) (hs : sigma.PosSemidef)
    (hn : rho ≠ 0) (hd : Dominates sigma rho) :
    Tendsto (fun a : ℝ => divergence a rho sigma) atTop (𝓝 (maxRelative rho sigma)) ∧
    Tendsto (fun a : ℝ => divergence a rho sigma) (𝓝[<] 1) (𝓝 (relative rho sigma)) ∧
    Tendsto (fun a : ℝ => divergence a rho sigma) (𝓝[>] 1) (𝓝 (relative rho sigma)) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P35

end
