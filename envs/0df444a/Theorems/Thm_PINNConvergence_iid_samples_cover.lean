-- Prove2me | Theorems.Thm_PINNConvergence_iid_samples_cover
-- name    : PINNConvergence.iid_samples_cover
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-23T20:05:58.100615+00:00
-- url     : https://prove2.me/theorems/cb43c575-5dd5-4f8b-80b1-4777cb32358e
-- title:
--   Lemma B.2: iid samples fill the domain
-- statement:
--   Let $X\subset\mathbb{R}^d$ be compact and let $\mu$ be a probability measure supported on $X$ with density $\rho$ with respect to $s$-dimensional Hausdorff measure on $X$ ($s\ge1$), $\inf_X\rho>0$. Let $c>0$, and suppose that for every $\varepsilon>0$ with $c\varepsilon^s\le1$ there is a finite partition $\{X_k\}$ of $X$ into measurable sets with $\mu(X_k)\ge c\varepsilon^s$, each contained in a cube $H_\varepsilon(z_k)$ of side length $\varepsilon$ centred at some $z_k\in X_k$. Then for every $n\ge1$, with probability at least
--
--   $$1-\sqrt n\,\Big(1-\frac1{\sqrt n}\Big)^n$$
--
--   over $n$ iid samples $x_1,\dots,x_n$ from $\mu$, every $x\in X$ has a sample $x_j$ with $\|x-x_j\|\le\sqrt d\,c^{-1/s}n^{-1/(2s)}$.
--
--   This probabilistic space-filling estimate is the source of the convergence rates in Theorem 3.1.
--
--   **Formalization Note** The paper asks for the partitions for every $\varepsilon>0$. That hypothesis can never hold, because $\mu(X_k)\le1<c\varepsilon^s$ for large $\varepsilon$. It is therefore required only for $c\varepsilon^s\le1$; the proof uses only $c\varepsilon^s=n^{-1/2}$. The probability is the (outer) measure of the covering event under the product measure $\mu^{\otimes n}$.
-- source:
--   Shin, Darbon and Karniadakis, On the convergence of physics informed neural networks for linear second-order elliptic and parabolic type PDEs, arXiv:2004.01806v2 (2020), Appendix B, Lemma B.2, p. 23

import Mathlib
import Definitions.Def_PINNConvergence_Basic

open MeasureTheory Filter Topology

namespace PINNConvergence

theorem iid_samples_cover {d s : ℕ} (hs : 1 ≤ s) (X : Set (Rd d)) (hX : IsCompact X)
    (μ : Measure (Rd d)) (hμ1 : IsProbabilityMeasure μ) (hsupp : μ Xᶜ = 0)
    (ρ : Rd d → ENNReal) (hρ : Measurable ρ)
    (hμ : μ = ((Measure.hausdorffMeasure (s : ℝ)).restrict X).withDensity ρ)
    (hρpos : ∃ ρ₀ : ENNReal, 0 < ρ₀ ∧ ∀ x ∈ X, ρ₀ ≤ ρ x)
    (c : ℝ) (hc : 0 < c) (hpart : HasCubePartitions X μ c s) (N : ℕ) (hN : 1 ≤ N) :
    ENNReal.ofReal (1 - Real.sqrt N * (1 - 1 / Real.sqrt N) ^ N) ≤
      Measure.pi (fun _ : Fin N => μ)
        {xs | ∀ x ∈ X, ∃ j, dist x (xs j) ≤
          Real.sqrt d * c ^ (-(1 : ℝ) / s) * (N : ℝ) ^ (-(1 : ℝ) / (2 * s))} := by sorry

end PINNConvergence
