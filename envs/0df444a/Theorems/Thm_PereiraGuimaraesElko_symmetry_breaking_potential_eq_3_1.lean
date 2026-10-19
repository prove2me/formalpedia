-- Prove2me | Theorems.Thm_PereiraGuimaraesElko_symmetry_breaking_potential_eq_3_1
-- name    : PereiraGuimaraesElko.symmetry_breaking_potential_eq_3_1
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-12T12:52:06.731816+00:00
-- url     : https://prove2.me/theorems/c9997126-1d90-415c-8d39-0ac66bbbfcfc
-- title:
--   Eq. (3.1): the shifted symmetry-breaking potential, its minimum at $\Phi=\sigma$ and mass $m=\sqrt2\,\mu$
-- statement:
--   Let $v_0\ge0$, $\Lambda>0$, $\sigma>0$ and put
--   $$V_0=v_0+\Lambda^4,\qquad \mu=\frac{2\Lambda^2}{\sigma},\qquad \alpha=\frac{4\Lambda^4}{\sigma^4},\qquad m=\sqrt2\,\mu.$$
--   Let $V(\Phi)=v_0+\Lambda^4\left(1-\dfrac{\Phi^2}{\sigma^2}\right)^2$. Then:
--
--   1. for every $\Phi$,
--   $$V(\Phi)=V_0-\frac12\mu^2\Phi^2+\frac\alpha4\Phi^4;\qquad(3.1)$$
--   2. $V$ attains its global minimum at $\Phi=\sigma$, i.e. $V(\sigma)\le V(\Phi)$ for all $\Phi$;
--   3. the minimum value is $V(\sigma)=v_0$ (so it is zero when $v_0=0$);
--   4. the curvature at the minimum is $V''(\sigma)=m^2$, i.e. the field has physical mass $m=\sqrt2\,\mu$.
--
--   This is the potential that drives all three phases (inflation, matter-like oscillation, late acceleration through the constant $v_0$) in the paper.
--
--   **Formalization Note** The source's additional size condition $v_0\ll\Lambda^4$ is qualitative and is not formalized; it plays no role in these identities.
-- source:
--   S. H. Pereira and T. M. Guimarães, "From inflation to recent cosmic acceleration: the fermionic Elko field driving the evolution of the universe", JCAP 09 (2017) 038, https://doi.org/10.1088/1475-7516/2017/09/038 (arXiv:1702.07385), p. 6, Eq. (3.1) and the following paragraph

import Mathlib

namespace PereiraGuimaraesElko

theorem symmetry_breaking_potential_eq_3_1 (v₀ Λ σ V₀ μ α m : ℝ)
    (hv₀ : 0 ≤ v₀) (hΛ : 0 < Λ) (hσ : 0 < σ)
    (hV₀ : V₀ = v₀ + Λ ^ 4) (hμ : μ = 2 * Λ ^ 2 / σ) (hα : α = 4 * Λ ^ 4 / σ ^ 4)
    (hm : m = Real.sqrt 2 * μ)
    (V : ℝ → ℝ) (hV : ∀ Φ, V Φ = v₀ + Λ ^ 4 * (1 - Φ ^ 2 / σ ^ 2) ^ 2) :
    (∀ Φ, V Φ = V₀ - 1 / 2 * μ ^ 2 * Φ ^ 2 + α / 4 * Φ ^ 4) ∧
      (∀ Φ, V σ ≤ V Φ) ∧ V σ = v₀ ∧
      deriv (deriv V) σ = m ^ 2 := by
  sorry

end PereiraGuimaraesElko
