-- Prove2me | Theorems.Thm_RSCarrier_integrable_and_rsLocalIntegral_mul_left_eq_of_forall_lintegral_conj_eq
-- name    : RSCarrier.integrable_and_rsLocalIntegral_mul_left_eq_of_forall_lintegral_conj_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.566428+00:00
-- url     : https://prove2.me/theorems/4b7f4239-7f87-51e3-8b2a-3ad8d3233345
-- title:
--   Left translation invariance of the Rankin–Selberg carrier integral
-- statement:
--   Let $G$ be a second-countable, locally compact topological group with its Borel $\sigma$-algebra, $\mu$ a left Haar measure on $G$, and $H \le G$ a closed subgroup carrying a measure $\mu_H$ that is both a Haar measure and right invariant. Let $a \in G$ satisfy $x \in H \iff a x a^{-1} \in H$ for all $x \in G$, and assume conjugation by $a$ preserves $\mu_H$ in the sense that $\int^-_H \varphi(a x a^{-1})\,d\mu_H = \int^-_H \varphi\,d\mu_H$ for every measurable $\varphi : H \to [0,\infty]$. Let $\delta : G \to \mathbb{R}$ satisfy $\delta(hg) = \delta(g)$ for $h \in H$ and $\delta(ag) = \delta(g)$, let $s \in \mathbb{C}$, and let $W, F : G \to \mathbb{C}$ have left $H$-invariant product, $W(hg)F(hg) = W(g)F(g)$. Write $\nu$ for $\mu$ weighted by the density $g \mapsto w(g)\big/\int^-_H w(xg)\,d\mu_H(x)$, where $w$ is the explicit weight attached to $H$ and $\mu_H$ (a sum over $n$ of $2^{-n}(1 + \mu_H(\iota^{-1}(K_{n+1}K_{n+1}^{-1})))^{-1}$ times the indicator of $\operatorname{int} K_{n+1}$ for a chosen compact exhaustion $(K_n)$ when $G$ is $\sigma$-compact and weakly locally compact, and $0$ otherwise). If $g \mapsto W(g)F(g)\,\delta(g)^{s-1/2}$ is measurable and $\nu$-integrable, then $g \mapsto W(ag)F(ag)\,\delta(g)^{s-1/2}$ is $\nu$-integrable and the two $\nu$-integrals agree, i.e. the local integral attached to $(W, F)$ equals that attached to $(W(a\,\cdot), F(a\,\cdot))$.
--
--   This is the invariance of the quotient integral over $H \backslash G$, realised concretely as an integral against a density-weighted Haar measure on $G$, under left translation by an element of the normaliser of $H$ acting on $H$ with trivial modulus. It is used in the computation of the local Rankin–Selberg integrals of Jacquet–Whittaker functions on $\mathrm{GL}_2$ of a local field, where $H$ is the upper unipotent subgroup, by [`LanglandsTunnell.RankinSelberg.exists_rsLocalIntegral_jacquetWhittaker3_iotaGL_eq_sum_and_dual_eq_mul_sum_of_chamber_ed2`](thm.html#LanglandsTunnell.RankinSelberg.exists_rsLocalIntegral_jacquetWhittaker3_iotaGL_eq_sum_and_dual_eq_mul_sum_of_chamber_ed2).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_RSCarrier_integrable_and_rsLocalIntegral_mul_left_eq_of_forall_lintegral_conj_eq.lean

import Mathlib
import Definitions.Def_HaarQuotient
import Definitions.Def_LanglandsTunnell_RSCarrier

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory

theorem RSCarrier.integrable_and_rsLocalIntegral_mul_left_eq_of_forall_lintegral_conj_eq
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsHaarMeasure]
    (H : Subgroup G) (hH : IsClosed (H : Set G))
    (μH : Measure H) [μH.IsHaarMeasure] [μH.IsMulRightInvariant]
    (a : G) (ha : ∀ x : G, x ∈ H ↔ a * x * a⁻¹ ∈ H)
    (haμ : ∀ φ : H → ENNReal, Measurable φ →
      ∫⁻ x : H, φ ⟨a * (x : G) * a⁻¹, (ha (x : G)).1 x.2⟩ ∂μH = ∫⁻ x : H, φ x ∂μH)
    (δ : G → ℝ) (hδH : ∀ h ∈ H, ∀ g : G, δ (h * g) = δ g) (hδa : ∀ g : G, δ (a * g) = δ g)
    (s : ℂ) (W F : G → ℂ)
    (hWF : ∀ h ∈ H, ∀ g : G, W (h * g) * F (h * g) = W g * F g)
    (hmeas : Measurable (fun g : G => (W g * F g) * ((δ g : ℝ) : ℂ) ^ (s - 1 / 2)))
    (hint : Integrable (fun g : G => (W g * F g) * ((δ g : ℝ) : ℂ) ^ (s - 1 / 2))
      (μ.withDensity (HaarQuotient.density H μH))) :
    Integrable (fun g : G => (W (a * g) * F (a * g)) * ((δ g : ℝ) : ℂ) ^ (s - 1 / 2))
        (μ.withDensity (HaarQuotient.density H μH)) ∧
      RSCarrier.rsLocalIntegral μ H μH δ s (fun g => W (a * g)) (fun g => F (a * g)) =
        RSCarrier.rsLocalIntegral μ H μH δ s W F := by sorry
