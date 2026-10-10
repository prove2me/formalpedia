-- Prove2me | Theorems.Thm_SmoothCCP_Asymptotic_smoothCdf_uniform_cdf
-- name    : SmoothCCP.Asymptotic.smoothCdf_uniform_cdf
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T13:45:56.580193+00:00
-- url     : https://prove2.me/theorems/34b0414e-01b2-4173-b971-c4ea57361445
-- title:
--   Proof of Theorem 3.4, p. 10 — F_ε(0;x) → F(0;x) uniformly on compact U ⊆ X as ε → 0⁺
-- statement:
--   This is the smoothing-removal step in the proof of Theorem 3.4.
--
--   Let $X \subseteq \mathbb R^n$ be closed and let $C$ satisfy Assumptions 3.1 and 3.2: for each $x \in X$, $C(x,\cdot)$ is measurable and $\mathbb P_\xi(C(x,\xi) = y) = 0$ for every $y$, and $C(\cdot,\xi)$ is continuous for $\mathbb P_\xi$-almost every $\xi$. For every $\varepsilon > 0$ let $\gamma_\varepsilon$ be admissible. Then for every compact $U \subseteq X$,
--   $$\sup_{x\in U}\ \bigl|F_\varepsilon(0;x) - F(0;x)\bigr| \longrightarrow 0 \quad\text{as } \varepsilon \to 0^+,$$
--   where $F_\varepsilon(0;x) = \int \Gamma_\varepsilon(C(x,\xi))\,d\mathbb P_\xi$ and $F(0;x) = \mathbb P_\xi(C(x,\xi) \le 0)$.
--
--   This statement involves no sample. Combined with the uniform law of large numbers step, it gives Theorem 3.4.
--
--   **Formalization Note** The limit is taken along $\varepsilon \to 0$ with $\varepsilon > 0$, since $\Gamma_\varepsilon$ of (2.2) needs $\varepsilon > 0$. The family $\gamma_\varepsilon$ is arbitrary across $\varepsilon$.
-- source:
--   Peña-Ordieres, Luedtke, Wächter, Solving chance-constrained problems via a smooth sample-based nonlinear approximation, arXiv:1905.07377v2, proof of Theorem 3.4, p. 10, fifth paragraph

import Mathlib
import Definitions.Def_SmoothCCP_Feasibility_Setting

open MeasureTheory Filter Topology

namespace SmoothCCP.Asymptotic

/-- Proof of Theorem 3.4, p. 10, second half: F_ε(0; x) → F(0; x) uniformly on every compact
U ⊆ X as ε → 0⁺. -/
theorem smoothCdf_uniform_cdf
    {n : ℕ} {Ξ : Type} [MeasurableSpace Ξ] (Pξ : Measure Ξ) [IsProbabilityMeasure Pξ]
    (X : Set (Fin n → ℝ)) (hX : IsClosed X) (C : (Fin n → ℝ) → Ξ → ℝ)
    (hA31 : ∀ x ∈ X, ∀ y : ℝ, Pξ {s | C x s = y} = 0)
    (hA32meas : ∀ x ∈ X, Measurable (C x))
    (hA32cont : ∀ᵐ s ∂Pξ, Continuous (fun x => C x s))
    (γ : ℝ → ℝ → ℝ) (hγ : ∀ ε > 0, SmoothCCP.Feasibility.AdmissibleGamma ε (γ ε))
    (U : Set (Fin n → ℝ)) (hU : IsCompact U) (hUX : U ⊆ X) :
    TendstoUniformlyOn (fun (ε : ℝ) (x : Fin n → ℝ) => SmoothCCP.Feasibility.smoothCdf Pξ C ε (γ ε) 0 x)
      (fun x => SmoothCCP.Feasibility.cdf Pξ C 0 x) (𝓝[>] (0 : ℝ)) U := by sorry

end SmoothCCP.Asymptotic
