-- Prove2me | Theorems.Thm_RSCarrier_rsLocalIntegral_comp_mul_right_eq_mul_rsLocalIntegral_of_map_mul_right_eq
-- name    : RSCarrier.rsLocalIntegral_comp_mul_right_eq_mul_rsLocalIntegral_of_map_mul_right_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.566428+00:00
-- url     : https://prove2.me/theorems/208122a2-2aa8-5617-a825-96a96a565b56
-- title:
--   Right translation of the partner in the Rankin–Selberg carrier integral
-- statement:
--   Let $G$ be a second countable, locally compact topological group with its Borel $\sigma$-algebra, let $\mu$ be an s-finite left invariant measure on $G$, let $H \le G$ be a subgroup whose underlying set is closed, and let $\mu_H$ be an s-finite right invariant Haar measure on $H$. Let $h \in G$ be such that push-forward along $(\cdot * h)$ leaves $\mu$ unchanged. Let $\delta : G \to \mathbb{R}$ be measurable, strictly positive, multiplicative ($\delta(gk) = \delta(g)\delta(k)$) and left $H$-invariant ($\delta(xg) = \delta(g)$ for $x \in H$). Let $s \in \mathbb{C}$ and let $W, F : G \to \mathbb{C}$ be measurable and satisfy the two-point law $W(xg)F(xk) = W(g)F(k)$ for all $x \in H$ and $g, k \in G$. Write $\nu = \mu$ weighted by the density [`HaarQuotient.density H μH`](def/HaarQuotient.html#L25), that is by $g \mapsto \mathrm{weight}(g) / \int^-_{x \in H} \mathrm{weight}(xg)\,d\mu_H$, where $\mathrm{weight}$ is the explicit series $\sum_n 2^{-n}(1 + \mu_H(\iota^{-1}(K_{n+1}K_{n+1}^{-1})))^{-1}\mathbf{1}_{\operatorname{int} K_{n+1}}$ built from a compact exhaustion $(K_n)$ of $G$ (and $0$ unless $G$ is $\sigma$-compact and weakly locally compact). Then two things hold: first, $g \mapsto W(g)F(gh)\,\delta(g)^{s-1/2}$ is $\nu$-integrable if and only if $g \mapsto W(gh^{-1})F(g)\,\delta(g)^{s-1/2}$ is; second, the carrier integrals $\mathrm{rsLocalIntegral}$, namely $\int (W\cdot F)(g)\,\delta(g)^{s-1/2}\,d\nu$, satisfy $$\mathrm{rsLocalIntegral}(s; W, F(\cdot\, h)) = \delta(h^{-1})^{s-1/2}\,\mathrm{rsLocalIntegral}(s; W(\cdot\, h^{-1}), F).$$
--
--   This is the change of variables $g \mapsto gh^{-1}$ inside the local Rankin–Selberg integral taken over $G$ against the quotient density attached to the closed subgroup $H$, allowing a right translation to be transferred from the partner function $F$ to the Whittaker function $W$ at the cost of the factor $\delta(h^{-1})^{s-1/2}$. It is used in the Langlands–Tunnell strand, for instance when comparing translates of a Godement section and when expanding a finite sum of translates at level one.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_RSCarrier_rsLocalIntegral_comp_mul_right_eq_mul_rsLocalIntegral_of_map_mul_right_eq.lean

import Definitions.Def_HaarQuotient
import Definitions.Def_LanglandsTunnell_RSCarrier

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open MeasureTheory

theorem RSCarrier.rsLocalIntegral_comp_mul_right_eq_mul_rsLocalIntegral_of_map_mul_right_eq
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsMulLeftInvariant] [SFinite μ]
    (H : Subgroup G) (hH : IsClosed (H : Set G))
    (μH : Measure H) [μH.IsHaarMeasure] [μH.IsMulRightInvariant] [SFinite μH]
    (h : G) (hμh : Measure.map (· * h) μ = μ)
    (δ : G → ℝ) (hδ : Measurable δ) (hδpos : ∀ g : G, 0 < δ g) (hδmul : ∀ g k : G, δ (g * k) = δ g * δ k)
    (hδH : ∀ x ∈ H, ∀ g : G, δ (x * g) = δ g)
    (s : ℂ) (W F : G → ℂ) (hW : Measurable W) (hF : Measurable F)
    (hWF : ∀ x ∈ H, ∀ g k : G, W (x * g) * F (x * k) = W g * F k) :
    (Integrable (fun g : G => (W g * F (g * h)) * ((δ g : ℝ) : ℂ) ^ (s - 1 / 2)) (μ.withDensity (HaarQuotient.density H
      μH)) ↔ Integrable (fun g : G => (W (g * h⁻¹) * F g) * ((δ g : ℝ) : ℂ) ^ (s - 1 / 2)) (μ.withDensity
      (HaarQuotient.density H μH))) ∧
      RSCarrier.rsLocalIntegral μ H μH δ s W (fun g => F (g * h)) = ((δ h⁻¹ : ℝ) : ℂ) ^ (s - 1 / 2) *
        RSCarrier.rsLocalIntegral μ H μH δ s (fun g => W (g * h⁻¹)) F := by sorry
