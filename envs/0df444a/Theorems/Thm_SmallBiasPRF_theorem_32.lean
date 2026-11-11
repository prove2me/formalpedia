-- Prove2me | Theorems.Thm_SmallBiasPRF_theorem_32
-- name    : SmallBiasPRF.theorem_32
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T09:11:40.800618+00:00
-- url     : https://prove2.me/theorems/a425d37f-0955-4240-a6fe-651dffa9305a
-- title:
--   Theorem 32 — operator amplification via expander walks
-- statement:
--   Let $\Omega_0$ be a finite set and $\Gamma_0$ an undirected regular multigraph on $\Omega_0$ that is a $\lambda_0$-spectral expander with $\lambda_0\le1$. For $m\ge1$ let $\mu^m$ be the stationary walk distribution on $\Omega_0^m$. Let $\mathcal H$ be a Hilbert space and $f_j:\Omega_0\to B(\mathcal H)$, $j\in[m]$, operator-valued functions with $\max_{y}\|f_j(y)\|_{op}\le1$. Let $\gamma\in[0,1]$ and $J_0\subseteq[m]$ nonempty with $\|\mathbb E_{y\in\Omega_0}[f_j(y)]\|_{op}\le\gamma$ for every $j\in J_0$. With $\theta=1-(1-\lambda_0)^2(1-\gamma)$,
--
--   $$\Big\|\mathop{\mathbb E}_{(y_1,\dots,y_m)\sim\mu^m}\big[f_1(y_1)\cdots f_m(y_m)\big]\Big\|_{op}\ \le\ \theta^{|J_0|/2}.$$
--
--   This variant of Jeronimo–Mittal–Roy–Wigderson (Theorem 3.6 there, with $f_1=\dots=f_m$ and no set $J_0$) lets the expander walk replace independent uniform selectors at the cost of the factor $(1-\lambda_0)^2$.
--
--   **Formalization Note** $\Gamma_0$ is a neighbour function $NB_0:\Omega_0\times[d_0]\to\Omega_0$ with $d_0\ge1$; the walk law is $\mu^m(y)=|\Omega_0|^{-1}\prod_iE[y_i,y_{i+1}]$. The product of operators is composition, left to right. $\theta^{|J_0|/2}$ is a real power.
--
--   Differences from the source:
--   - generalization: Γ a finite undirected d-regular multigraph on [m₁] with labelled incidences → NB : Fin m₁ → Fin d → Fin m₁ with symmetric incidence counts #{e : NB x e = y} = #{e : NB y e = x} (IsUndirected); reason: the proof uses only the symmetry and regularity of the adjacency matrix; every undirected d-regular multigraph satisfies the condition, which in addition admits an odd number of loop incidences at a vertex
--   - encoding: the second largest singular value of the normalized adjacency matrix is at most λ₀ → ‖adjMatrix NB₀ − avgMatrix‖ ≤ λ₀ (IsSpectralExpander); reason: for a symmetric stochastic matrix the second largest singular value is ‖E − U‖_op, the definition the paper uses (p.16); same instances
--   - generalization: H a Hilbert space (real in the application H = L²(W)) → a complete inner product space over any RCLike field 𝕜 (ℝ or ℂ); reason: the theorem holds verbatim over ℝ and over ℂ; both readings of “Hilbert space” are covered
--   - encoding: the stationary walk distribution μ^m (uniform initial vertex, each step one transition of E_Γ) and the expectation of f₁(y₁)⋯f_m(y_m) under it → walkLaw NB m y = |Ω|⁻¹ ∏_{i+1<m} E_Γ[y_i, y_{i+1}] and Σ_y walkLaw(y) · (List.ofFn …).prod, leftmost factor = coordinate 1; reason: the law of the stationary chain with transition matrix E_Γ, products in chronological order; same distribution and same operator
-- source:
--   Dinur–Ishai, Towards Asymptotically Optimal Pseudorandom Functions: Linear-Size Circuits with Exponentially Small Bias, STOC 2027 submission (version of 2026-11-03, sha256 65dbd47e…), Theorem 32, p.38 (PDF 41); proof Appendix B, pp.48–52 (PDF 51–55)

import Mathlib
import Definitions.Def_SmallBiasPRF_IsSpectralExpander

namespace SmallBiasPRF

/-- **Theorem 32** (operator amplification via expander walks; a variant of [JMRW25, Theorem 3.6]),
p.38 (PDF p.41); proved in Appendix B, pp.48–52.
Dinur–Ishai, *Towards Asymptotically Optimal Pseudorandom Functions: Linear-Size Circuits with
Exponentially Small Bias*, STOC 2027 submission (version of 2026-11-03, sha256 65dbd47e…), Theorem 32, p.38 (PDF p.41).

Let `Ω₀` be a finite space and `Γ₀` an undirected regular multigraph on `Ω₀` that is a
`λ₀`-spectral expander (second largest singular value of its normalized adjacency matrix at most
`λ₀ ≤ 1`). For `m ≥ 1` let `μ^m` be the stationary walk distribution on `Ω₀^m`. Let `H` be a
Hilbert space and `f_j : Ω₀ → B(H)`, `j ∈ [m]`, with `max_y ‖f_j(y)‖_op ≤ 1`. Let `γ ∈ [0, 1]`
and `J₀ ⊆ [m]` nonempty with `‖E_{y∈Ω₀}[f_j(y)]‖_op ≤ γ` for every `j ∈ J₀`. With
`θ = 1 − (1 − λ₀)²(1 − γ)`,
`‖E_{(y₁,…,y_m)∼μ^m}[f₁(y₁) ⋯ f_m(y_m)]‖_op ≤ θ^{|J₀|/2}`.

**Formalization Note.** `Γ₀` is a neighbour function `NB₀ : Ω₀ → Fin d₀ → Ω₀` with `d₀ ≥ 1` and
symmetric incidence counts; the spectral condition is `‖E − U‖_op ≤ λ₀` (`lam₀` in Lean), which for a symmetric
`E` is the second largest singular value. `μ^m` is `walkLaw` (uniform start, transitions of
`E`). The Hilbert space is over any `RCLike` field `𝕜` (`ℝ` or `ℂ`); bounded operators are
`H →L[𝕜] H` with composition as product, taken left to right (`List.ofFn`, index `0` = `f₁`).
`θ^{|J₀|/2}` is a real power. -/
theorem theorem_32 {Ω₀ : Type*} [Fintype Ω₀] [DecidableEq Ω₀] [Nonempty Ω₀] {d₀ : ℕ} [NeZero d₀]
    (NB₀ : Ω₀ → Fin d₀ → Ω₀) (hund : IsUndirected NB₀) (lam₀ : ℝ)
    (hspec : IsSpectralExpander NB₀ lam₀) (hlam₀ : lam₀ ≤ 1) (m : ℕ) (hm : 1 ≤ m)
    {𝕜 : Type*} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    [CompleteSpace E] (f : Fin m → Ω₀ → (E →L[𝕜] E)) (hf : ∀ j y, ‖f j y‖ ≤ 1)
    (γ : ℝ) (hγ₀ : 0 ≤ γ) (hγ₁ : γ ≤ 1) (J₀ : Finset (Fin m)) (hJ₀ : J₀.Nonempty)
    (hJ : ∀ j ∈ J₀, ‖((Fintype.card Ω₀ : 𝕜)⁻¹) • ∑ y, f j y‖ ≤ γ) :
    ‖∑ y : Fin m → Ω₀, ((walkLaw NB₀ m y : ℝ) : 𝕜) • (List.ofFn fun j => f j (y j)).prod‖ ≤
      (1 - (1 - lam₀) ^ 2 * (1 - γ)) ^ ((J₀.card : ℝ) / 2) := by sorry

end SmallBiasPRF
