-- Prove2me | Theorems.Thm_TargetGranularity_SdVsMd_proposition_2
-- name    : TargetGranularity.SdVsMd.proposition_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:03:49.134084+00:00
-- url     : https://prove2.me/theorems/2bc0e897-77a5-4659-80db-94b9bc87d4a9
-- title:
--   Proposition 2, p. 18 (PDF 19), case c_ad < min{p², p(1−p)} of (7) — unique symmetric md equilibrium Σmd(γ1*,1/γ1*) iff c_click ≤ c^max_click
-- statement:
--   Let $0<p<1$, $0<c_{ad}<\min\{p^2,p(1-p)\}$, $c_{click}>0$, and $\gamma_1^*=-\frac{c_{ad}}{p-c_{ad}}$, and write $c^{max}_{click}(c_{ad},p)$ for the threshold of Equation (7), here in its third case
--   $$c^{max}_{click}(c_{ad},p)=\frac{c_{ad}^2-3c_{ad}(1-p)p+3(1-p)^2p^2}{6p\,(p(1-p)(1+p)-c_{ad})}.$$
--
--   1. If $c_{click}\le c^{max}_{click}(c_{ad},p)$, then $\Sigma^{md}(\gamma_1^*,1/\gamma_1^*)$ is a non-trivial symmetric md equilibrium; its click set is $[0,\underline\omega]\cup[1-\underline\omega,1]$ for some $0\le\underline\omega\le\frac12$; and every non-trivial symmetric md equilibrium coincides with $\Sigma^{md}(\gamma_1^*,1/\gamma_1^*)$ up to a null set.
--   2. If $c_{click}>c^{max}_{click}(c_{ad},p)$, there is no non-trivial symmetric md equilibrium.
--
--   Part 2 is the converse stated in the proof of Lemma 5 (pp. 40–41): "for $c_{click}>c^{max}_{click}$, there is no non-trivial symmetric equilibrium." Together the two parts make $c^{max}_{click}$ the exact boundary of the symmetric md equilibrium, which is the md half of the comparison in Proposition 3.
--
--   **Formalization Note** The statement is restricted to the case $c_{ad}<\min\{p^2,p(1-p)\}$ of Equation (7), the only case Proposition 3 uses; the page's hypothesis is $c_{ad}\le p$. Note $1/\gamma_1^*=-\frac{p-c_{ad}}{c_{ad}}=\gamma_2^*$. Uniqueness is up to null sets. The page writes "$\Omega^{*md}\in$" for "$=$".
-- source:
--   Despotakis & Yu, Multidimensional Targeting and Consumer Response, SSRN 3900394 (version of October 11, 2022), p. 18 (PDF 19), Proposition 2; proof of Lemma 5, pp. 40–41 (PDF 41–42), Equation (7) and the converse

import Mathlib
import Definitions.Def_TargetGranularity_SdVsMd_Model

namespace TargetGranularity.SdVsMd

/-- Proposition 2, p. 18, in the case `c_ad < min{p², p(1−p)}` of Equation (7), with the converse
from the proof of Lemma 5 (p. 40): with `γ₁* = −c_ad/(p − c_ad)`, if `c_click ≤ c^max_click(c_ad, p)`
then `Σ^md(γ₁*, 1/γ₁*)` is a non-trivial symmetric md equilibrium, its click set is
`[0, ω̲] ∪ [1 − ω̲, 1]` for some `0 ≤ ω̲ ≤ 1/2`, and every non-trivial symmetric md equilibrium
equals it up to a null set; if `c_click > c^max_click(c_ad, p)` there is none. -/
theorem proposition_2 (p cad cclick : ℝ) (hp0 : 0 < p) (hp1 : p < 1) (hcad : 0 < cad)
    (hcadp2 : cad < p ^ 2) (hcadp1 : cad < p * (1 - p)) (hcclick : 0 < cclick) :
    (cclick ≤ cmaxClick cad p →
      IsSymMdEq p cad cclick (mdSet p (-(cad / (p - cad))) (1 / (-(cad / (p - cad))))) ∧
      (∃ ωlo : ℝ, 0 ≤ ωlo ∧ ωlo ≤ 1 / 2 ∧
        mdClick p cclick (mdSet p (-(cad / (p - cad))) (1 / (-(cad / (p - cad))))) =
          Set.Icc 0 ωlo ∪ Set.Icc (1 - ωlo) 1) ∧
      ∀ S : Set (ℝ × ℝ), IsSymMdEq p cad cclick S →
        S =ᵐ[MeasureTheory.volume] mdSet p (-(cad / (p - cad))) (1 / (-(cad / (p - cad))))) ∧
    (cmaxClick cad p < cclick → ¬ ∃ S : Set (ℝ × ℝ), IsSymMdEq p cad cclick S) := by sorry

end TargetGranularity.SdVsMd
