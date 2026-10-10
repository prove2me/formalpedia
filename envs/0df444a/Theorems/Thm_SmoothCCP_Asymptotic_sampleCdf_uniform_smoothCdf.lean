-- Prove2me | Theorems.Thm_SmoothCCP_Asymptotic_sampleCdf_uniform_smoothCdf
-- name    : SmoothCCP.Asymptotic.sampleCdf_uniform_smoothCdf
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T13:45:41.218412+00:00
-- url     : https://prove2.me/theorems/da899e43-fb1b-4f76-bf4d-11749b78d494
-- title:
--   Proof of Theorem 3.4, p. 10 — w.p.1, F^N_ε(0;x) − F_ε(0;x) → 0 uniformly in x ∈ U, ε ∈ (0,1], as N → ∞
-- statement:
--   This is the uniform law of large numbers step in the proof of Theorem 3.4.
--
--   Let $X \subseteq \mathbb R^n$ be closed, let $\xi_1, \xi_2, \dots$ be an i.i.d. sequence with law $\mathbb P_\xi$ on $\Xi$, and let $C : \mathbb R^n \times \Xi \to \mathbb R$ satisfy:
--
--   1. (Assumption 3.1) for each $x \in X$, $C(x,\xi)$ has a continuous distribution: $\mathbb P_\xi(C(x,\xi) = y) = 0$ for every $y \in \mathbb R$;
--   2. (Assumption 3.2) $C(x,\cdot)$ is measurable for every $x \in X$, and $C(\cdot,\xi)$ is continuous for $\mathbb P_\xi$-almost every $\xi$.
--
--   For every $\varepsilon > 0$ let $\gamma_\varepsilon$ be admissible, with no relation imposed between different $\varepsilon$. Then for every compact $U \subseteq X$, with probability one,
--   $$\lim_{N\to\infty}\ \sup_{\varepsilon\in(0,1]}\ \sup_{x\in U}\ \bigl|F^N_\varepsilon(0;x) - F_\varepsilon(0;x)\bigr| = 0,$$
--   where $F^N_\varepsilon$ is built from the first $N$ draws $\xi_1,\dots,\xi_N$.
--
--   This is the first of the two halves into which the paper splits Theorem 3.4; the second removes the smoothing as $\varepsilon \to 0$.
--
--   **Formalization Note** The paper takes $\varepsilon \in [0,1]$, where $\varepsilon = 0$ is a device for continuity in $\varepsilon$; $\Gamma_0$ is not defined by (2.2), so the statement uses $\varepsilon \in (0,1]$. The single null set is chosen before $\eta$, $\varepsilon$ and $x$. The sup over $\varepsilon$ and $x$ is written as "for every $\eta > 0$ there is $N_0$ with the bound $< \eta$ for all $N \ge N_0$, $\varepsilon \in (0,1]$, $x \in U$". Decisions carry the sup norm; the sample is an independent sequence of measurable maps on a probability space, each with law $\mathbb P_\xi$.
-- source:
--   Peña-Ordieres, Luedtke, Wächter, Solving chance-constrained problems via a smooth sample-based nonlinear approximation, arXiv:1905.07377v2, proof of Theorem 3.4, p. 10, first and fourth paragraphs

import Mathlib
import Definitions.Def_SmoothCCP_Feasibility_Setting

open MeasureTheory Filter Topology

namespace SmoothCCP.Asymptotic

/-- Proof of Theorem 3.4, p. 10, first half: w.p.1, F^N_ε(0; x) − F_ε(0; x) → 0 as N → ∞,
uniformly over x ∈ U and ε ∈ (0, 1], for every compact U ⊆ X. -/
theorem sampleCdf_uniform_smoothCdf
    {n : ℕ} {Ξ : Type} [MeasurableSpace Ξ] (Pξ : Measure Ξ) [IsProbabilityMeasure Pξ]
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (ξ : ℕ → Ω → Ξ) (hξmeas : ∀ i, Measurable (ξ i))
    (hξind : ProbabilityTheory.iIndepFun ξ P) (hξlaw : ∀ i, P.map (ξ i) = Pξ)
    (X : Set (Fin n → ℝ)) (hX : IsClosed X) (C : (Fin n → ℝ) → Ξ → ℝ)
    (hA31 : ∀ x ∈ X, ∀ y : ℝ, Pξ {s | C x s = y} = 0)
    (hA32meas : ∀ x ∈ X, Measurable (C x))
    (hA32cont : ∀ᵐ s ∂Pξ, Continuous (fun x => C x s))
    (γ : ℝ → ℝ → ℝ) (hγ : ∀ ε > 0, SmoothCCP.Feasibility.AdmissibleGamma ε (γ ε))
    (U : Set (Fin n → ℝ)) (hU : IsCompact U) (hUX : U ⊆ X) :
    ∀ᵐ ω ∂P, ∀ η > 0, ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ ε ∈ Set.Ioc (0 : ℝ) 1, ∀ x ∈ U,
      |SmoothCCP.Feasibility.sampleCdf C ε (γ ε) (fun i : Fin N => ξ i ω) 0 x - SmoothCCP.Feasibility.smoothCdf Pξ C ε (γ ε) 0 x| < η := by sorry

end SmoothCCP.Asymptotic
