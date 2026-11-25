-- Prove2me | Theorems.Thm_SteerableE2CNN_pointwise_nonlinearity_quotient_equivariant
-- name    : SteerableE2CNN.pointwise_nonlinearity_quotient_equivariant
-- status  : Proved
-- author  : @Xeroth
-- created : 2026-11-24T09:40:13.999565+00:00
-- url     : https://prove2.me/theorems/cf38fb93-359a-4dee-b302-a5a427663f6c
-- title:
--   Appendix D.2.3: pointwise nonlinearities are equivariant under quotient representations
-- statement:
--   Let $G$ be a finite group, $H\le G$ a subgroup, and $\rho_{\mathrm{quot}}^{G/H}$ the quotient representation on $\mathbb{R}^{|G|/|H|}$, which permutes the axes $e_{gH}$ by $\rho_{\mathrm{quot}}^{G/H}(\tilde g)e_{gH}=e_{\tilde ggH}$. Let $\sigma:\mathbb{R}\to\mathbb{R}$ be any function, and let $\sigma_{\mathrm{pt}}$ apply it to each entry of a vector. Then for every $\tilde g\in G$ and every $v\in\mathbb{R}^{|G|/|H|}$,
--
--   $$\sigma_{\mathrm{pt}}\big(\rho_{\mathrm{quot}}^{G/H}(\tilde g)v\big)=\rho_{\mathrm{quot}}^{G/H}(\tilde g)\,\sigma_{\mathrm{pt}}(v).$$
--
--   With $H=\{e\}$ this covers regular representations, which is why pointwise nonlinearities such as ReLU may be used on regular and quotient fields.
-- source:
--   Weiler and Cesa, General E(2)-Equivariant Steerable CNNs, arXiv:1911.08251v2 (NeurIPS 2019), Section 2.6, p. 6; Appendix D.2.3, p. 23

import Mathlib
import Definitions.Def_SteerableE2CNN_Basic

open Matrix MeasureTheory

namespace SteerableE2CNN

open Classical in
theorem pointwise_nonlinearity_quotient_equivariant {G : Type*} [Group G] [Fintype G]
    (H : Subgroup G) (σ : ℝ → ℝ) (g : G) (v : G ⧸ H → ℝ) :
    (fun a => σ ((quotRep H g *ᵥ v) a)) = quotRep H g *ᵥ (fun a => σ (v a)) := by sorry

end SteerableE2CNN
