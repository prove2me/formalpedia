-- Prove2me | Theorems.Thm_SelfStructIS_LogEff_lemma_A_4
-- name    : SelfStructIS.LogEff.lemma_A_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-13T23:30:29.472481+00:00
-- url     : https://prove2.me/theorems/53787128-bd57-4df4-9a72-0611e11b3af3
-- title:
--   Lemma A.4, p. 32 — y c_ρ(u) ≤ T⁻¹(y) ≤ min{y[c_ρ(u)]^{log y/log‖y‖∞} ∨ 1, ‖y‖∞ c_ρ(u)}
-- statement:
--   Let $T$ be the self-structuring transformation with exponent $\kappa^{(1)}$, growth index $\rho>0$ and $0<l<u$, and let $c_\rho(u)=(l/u)^{1/\rho}$. For every $y\in\mathbb R^d_+$ with $\|y\|_\infty\ge1/c_\rho(u)$, the preimage $x=T^{-1}(y)$ satisfies, componentwise,
--   $$y\,c_\rho(u)\ \le\ T^{-1}(y)\ \le\ \min\Big\{y\,[c_\rho(u)]^{\frac{\log y}{\log\|y\|_\infty}}\vee\mathbf 1,\ \ \|y\|_\infty\,c_\rho(u)\Big\}.$$
--
--   The two-sided bound controls how far back the sampler's inverse map pulls a point of the rare set; it drives the estimate of $\psi_u$ in Lemma A.5.
--
--   **Formalization Note** The bounds are stated for every $x$ with $T(x)=y$, which is equivalent to the $T^{-1}$ form because $T$ is injective (Proposition 2.1). The hypothesis $0<l<u$ (so $c_\rho(u)\in(0,1)$) is implicit in the paper. At $y_i=0$ the term $\log y_i$ is Lean's $0$; then $x_i=0$ and the bound reads $0\le\min\{1,\|y\|_\infty c_\rho(u)\}$, as in the paper, whose (46) sets $\tilde x_i=1$ when $y_i<1$.
-- source:
--   Deo, Murthy, Achieving Efficiency in Black-Box Simulation of Distribution Tails with Self-Structuring Importance Samplers, arXiv:2102.07060v3, p. 32, Lemma A.4, (45)

import Mathlib
import Definitions.Def_HeavyTailNV_Tail_Model
import Definitions.Def_SelfStructIS_LogEff_Setting
import Definitions.Def_SelfStructIS_LogEff_Sampler
import Definitions.Def_SelfStructIS_LogEff_Tail

open MeasureTheory Filter Topology

namespace SelfStructIS.LogEff

theorem lemma_A_4 (d : ℕ) (ρ u l : ℝ) (hρ : 0 < ρ) (hl : 0 < l) (hlu : l < u)
    (y : Fin d → ℝ) (hy : ∀ i, 0 ≤ y i) (hy_norm : 1 / cRho ρ u l ≤ ‖y‖)
    (x : Fin d → ℝ) (hx : Tmap .one ρ u l x = y) :
    (∀ i, y i * cRho ρ u l ≤ x i) ∧
      ∀ i, x i ≤ min (max (y i * cRho ρ u l ^ (Real.log (y i) / Real.log ‖y‖)) 1)
        (‖y‖ * cRho ρ u l) := by sorry

end SelfStructIS.LogEff
