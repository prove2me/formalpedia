-- Prove2me | Theorems.Thm_UnknownLoads_Refined_lemma_13
-- name    : UnknownLoads.Refined.lemma_13
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-13T22:37:26.415024+00:00
-- url     : https://prove2.me/theorems/cab20a54-6664-48b5-b441-136f0bef2a2c
-- title:
--   Lemma 13 — once q_k(j) = 1 with ℓ_k ≤ j, the threshold stays at j and q_k(j) ≥ 1 − k^{−γ}
-- statement:
--   Assume the hypotheses of Theorem 2 (condition (5) and $(m,\Delta)$-boundedness on $[a,b]$). Fix $\omega\in\Omega_T$ and $j\in\{i\Delta:0\le i\le m\}$. Let $\mathcal K\subset\mathbb N$ be increasing, $\varepsilon>0$, and $a+\varepsilon\le\zeta_{k,1}\le\zeta_{k,2}\le b$ ($k\in\mathcal K$) be times with
--   $$
--   q_k(\omega,\zeta_{k,1},j)=1\quad\text{and}\quad \ell_k(\omega,t)\le j\qquad\text{for all }t\in[\zeta_{k,1},\zeta_{k,2}]\text{ and }k\in\mathcal K .
--   $$
--   Then for every $\gamma\in[0,1/2)$ and all sufficiently large $k\in\mathcal K$,
--   $$
--   \ell_k(\omega,t)=j\quad\text{and}\quad q_k(\omega,t,j)\ge1-k^{-\gamma}\qquad\text{for all }t\in[\zeta_{k,1},\zeta_{k,2}].
--   $$
--
--   Once every pool holds at least $j\le m\Delta$ tasks and the threshold is at most $j$, the threshold locks at $j$ and the fraction of pools below $j$ is $o(k^{-\gamma})$; this gives (6a) and (6b).
--
--   Throughout, "for each $\omega\in\Omega_T$" is rendered as: for every constant $B_T$ and every outcome $\omega$ satisfying the nice-path predicate $\mathrm{IsNicePath}(B_T,\omega)$ of Proposition 7 (the standing initial conditions, the equations (9a)–(9b) with simple events for every $n\ge1$, the relative-compactness property of Proposition 4, (11) with some $n_T(\omega)$, and (12a)–(12c) for every $\gamma\in[0,1/2)$). Proposition 7 states that this predicate holds almost surely for some $B_T>0$.
--
--   **Formalization Note** The order is: for each $\gamma$, eventually in $k$ (the proof fixes $\gamma$ first). $k$ in $k^{-\gamma}$ is the system index $\varphi(k)$. Condition (5) is rendered as in Proposition 10.
-- source:
--   Goldsztajn, Borst & van Leeuwaarden, Learning and balancing unknown loads in large-scale systems, arXiv:2012.10142v3, p. 34, Lemma 13

import Mathlib
import Definitions.Def_BesbesZeevi_Parametric_PoissonProcess
import Definitions.Def_UnknownLoads_Refined_Load
import Definitions.Def_UnknownLoads_Refined_Construction
import Definitions.Def_UnknownLoads_Refined_System

open MeasureTheory ProbabilityTheory Set Filter Topology

namespace UnknownLoads.Refined

theorem lemma_13 (D : LoadData) {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {α : ℕ → ℝ}
    (sys : System D Ω P α)
    (γ₀ : ℝ) (hγ₀ : γ₀ ∈ Ioo (0 : ℝ) (1 / 2))
    (hα_lim : Tendsto α atTop (𝓝 1))
    (hα_rate : ∃ κ > (0 : ℝ), ∀ᶠ n : ℕ in atTop, κ ≤ (n : ℝ) ^ γ₀ * (1 - α n))
    (m : ℕ) (a b : ℝ) (hbd : D.IsBounded sys.q0 m a b)
    (BT : ℕ) (ω : Ω) (hω : sys.IsNicePath BT ω)
    (j : ℕ) (hj : ∃ i : ℕ, i ≤ m ∧ j = i * D.Δ)
    (φ : ℕ → ℕ) (hφ : StrictMono φ) (hφ₀ : 1 ≤ φ 0)
    (ε : ℝ) (hε : 0 < ε) (ζ₁ ζ₂ : ℕ → ℝ) (hζ : ∀ k, a + ε ≤ ζ₁ k ∧ ζ₁ k ≤ ζ₂ k ∧ ζ₂ k ≤ b)
    (hyp : ∀ k, sys.q (φ k) ω (ζ₁ k) j = 1 ∧ ∀ t ∈ Icc (ζ₁ k) (ζ₂ k), sys.ℓ (φ k) ω t ≤ j) :
    ∀ γ ∈ Ico (0 : ℝ) (1 / 2), ∀ᶠ k : ℕ in atTop, ∀ t ∈ Icc (ζ₁ k) (ζ₂ k),
      sys.ℓ (φ k) ω t = j ∧ 1 - (φ k : ℝ) ^ (-γ) ≤ sys.q (φ k) ω t j := by sorry

end UnknownLoads.Refined
