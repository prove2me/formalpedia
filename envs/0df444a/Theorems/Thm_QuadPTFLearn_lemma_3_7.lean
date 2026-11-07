-- Prove2me | Theorems.Thm_QuadPTFLearn_lemma_3_7
-- name    : QuadPTFLearn.lemma_3_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T03:25:38.233286+00:00
-- url     : https://prove2.me/theorems/604424ab-f3c3-4b5c-8aa6-df36b8e43b98
-- title:
--   Lemma 3.7, p.21 — Gaussian subspace transfer: $\Pr[f\ne g]\le Ck^C(\delta+\tau)^{1/20}$ with $g_i\in P_{\le2}(V)\oplus\{u\cdot\Phi_2:u\in W\}$
-- statement:
--   **Gaussian subspace transfer.** Let $\tau\in(0,1)$, $V\subseteq\mathbb R^d$ and $p_1,\dots,p_k$ polynomials of degree at most two with the decompositions and Gaussian replacements of Section 3, $\|p_i\|_2=1$ and coefficient norms $\|b_i\|_2,\|L_i\|_{op},\|A_i\|_{op}\le\tau$ (the assumptions of Lemma 3.3). Let $f(x)=1\{p_1(x)\ge0,\dots,p_k(x)\ge0\}$ and $\tilde f(x_V,z)=1\{q_i(x_V)+\theta_i\cdot z\ge0\text{ for all }i\}$. Let $\delta\in[0,1]$ and $W\subseteq S_V$ a subspace such that $\mathrm{Rand}_{\tilde f}(w)\le\delta$ for every unit vector $w\in W^\perp$, the complement taken within $S_V$.
--
--   Then there is an intersection $g(x)=1\{g_1(x)\ge0,\dots,g_k(x)\ge0\}$ with $g_i\in P_{\le2}(V)\oplus\{u\cdot\Phi_2(x):u\in W\}$ for every $i$, where $P_{\le2}(V)$ is the space of polynomials of degree at most two depending only on $x_V$, such that
--   $$\Pr_{x\sim N(0,I_d)}[f(x)\ne g(x)]\le Ck^C(\delta+\tau)^{1/20}$$
--   for a universal constant $C>1$.
--
--   A subspace that captures the label information of the Gaussian surrogate also supports a good approximation of the original intersection.
--
--   Differences from the source:
--   - encoding: the assumptions of Lemma 3.3 → `Lemma33Assumptions`: τ ∈ (0,1), deg p_i ≤ 2, ∥p_i∥₂ = 1, coefficient norms ≤ τ read off directional derivatives along V⊥; θ_i the Hermite coefficients of p_i − q_i(z); S_V the span of {θ : E[θ·Φ₂ | z] = 0}; reason: the same objects (see `QuadPTFLearn.Regularity`)
--   - encoding: Rand_{f̃}(w) in the (x_V, z) Gaussian model → E_{x∼N(0,I_d)}[Rand_{f̃(x,·)}(w)], the randomized error of the section G ↦ f̃(x, G) averaged over x; reason: Fubini: the same quantity, f̃ depending on x only through x_V
--   - encoding: g_i ∈ P_{≤2}(V) ⊕ {u · Φ₂(x) : u ∈ W} → g_i(x) = a_i(x) + ⟪u_i, Φ₂(x)⟫ with deg a_i ≤ 2, a_i(x) = a_i(proj_V x), u_i ∈ W; reason: the same space
--   - encoding: i ∈ [k], k ∈ ℤ₊ → k a natural number, k = 0 not excluded; reason: at k = 0 f = g ≡ 1 and the error is 0; no instance of the source changes
-- source:
--   Diakonikolas, Kane, Ma, Ren, Tran, Beyond Multi-Index Models: Learning Intersections of Degree-2 PTFs, arXiv:2611.05114 (sha256 4d6ea892…), Lemma 3.7 (Gaussian subspace transfer), p.21 (PDF p.23); assumptions of Lemma 3.3, p.16 (PDF p.18)

import Mathlib
import Definitions.Def_QuadPTFLearn_Regularity

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

namespace QuadPTFLearn

/-- I. Diakonikolas, D. M. Kane, M. Ma, L. Ren, T. Tran, *Beyond Multi-Index Models: Learning
Intersections of Degree-2 PTFs*, arXiv:2611.05114 (held copy, sha256 4d6ea892…5aed).
Lemma 3.7 (Gaussian subspace transfer), p.21 (PDF p.23).

Let `τ, V, p₁, …, p_k` satisfy the assumptions of Lemma 3.3: `τ ∈ (0, 1)`, each `pᵢ` of degree at
most two with `‖pᵢ‖₂ = 1` and coefficient norms `‖bᵢ‖₂, ‖Lᵢ‖_op, ‖Aᵢ‖_op ≤ τ`. Let
`f = 1{p₁ ≥ 0, …, p_k ≥ 0}`, `f̃(x_V, z) = 1{qᵢ(x_V) + θᵢ · z ≥ 0 ∀ i}`, `δ ∈ [0, 1]`, and
`W ⊆ S_V` a subspace with `Rand_{f̃}(w) ≤ δ` for every unit `w ∈ W⊥` (within `S_V`). Then there
is `g = 1{g₁ ≥ 0, …, g_k ≥ 0}` with `gᵢ ∈ P_{≤2}(V) ⊕ {u · Φ₂(x) : u ∈ W}` and
`Pr_{x∼N(0,I_d)}[f(x) ≠ g(x)] ≤ C k^C (δ + τ)^{1/20}`, for a universal `C > 1`. -/
theorem lemma_3_7 :
    ∃ C : ℝ, 1 < C ∧
      ∀ (d k : ℕ) (τ : ℝ) (V : Submodule ℝ (Pt d)) (p : Fin k → Poly d),
        Lemma33Assumptions τ V p →
      ∀ δ : ℝ, 0 ≤ δ → δ ≤ 1 → ∀ W : Submodule ℝ (Lift d), W ≤ SV V →
        (∀ w ∈ SV V, w ∈ Wᗮ → ‖w‖ = 1 → randSurrogate V p w ≤ δ) →
        ∃ a : Fin k → Poly d, ∃ u : Fin k → Lift d,
          (∀ i, (a i).totalDegree ≤ 2 ∧ DependsOnlyOn V (a i) ∧ u i ∈ W) ∧
          gauss d {x | ptfInd p x ≠
              (if ∀ i, 0 ≤ peval (a i) x + ⟪u i, phi2 x⟫ then (1 : ℝ) else 0)} ≤
            ENNReal.ofReal (C * (k : ℝ) ^ C * (δ + τ) ^ ((1 : ℝ) / 20)) := by sorry

end QuadPTFLearn
