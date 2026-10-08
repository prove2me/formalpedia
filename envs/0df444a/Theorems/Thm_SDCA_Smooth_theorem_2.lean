-- Prove2me | Theorems.Thm_SDCA_Smooth_theorem_2
-- name    : SDCA.Smooth.theorem_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T18:09:19.948156+00:00
-- url     : https://prove2.me/theorems/523f9421-e4de-4153-b16c-28a044f85839
-- title:
--   Theorem 2 — SDCA with $(1/\gamma)$-smooth losses reaches expected duality gap $\epsilon_P$ after $(n+\frac1{\lambda\gamma})\log((n+\frac1{\lambda\gamma})/\epsilon_P)$ iterations
-- statement:
--   Let $x_1,\dots,x_n\in\mathbb R^d$ with $n\ge1$, let $\lambda>0$ and $\gamma>0$, and let $\varphi_1,\dots,\varphi_n:\mathbb R\to\mathbb R$ be convex and $(1/\gamma)$-smooth (differentiable with $(1/\gamma)$-Lipschitz derivative). Assume the standing assumptions
--   1. $\|x_i\|\le1$ for all $i$,
--   2. $\varphi_i(a)\ge0$ for all $i$ and $a$,
--   3. $\varphi_i(0)\le1$ for all $i$.
--
--   Run Procedure SDCA from $\alpha^{(0)}=0$: at each iteration a coordinate $i$ is drawn uniformly at random, independently of the past, and $\alpha_i$ is changed by an increment maximizing the coordinate dual objective; $w^{(t)}=w(\alpha^{(t)})$. Let $\epsilon_P>0$. Then all dual values along the run and at the averaged output are finite, and:
--
--   1. **(Last iterate.)** If
--   $$T\ \ge\ \Big(n+\frac1{\lambda\gamma}\Big)\log\Big(\Big(n+\frac1{\lambda\gamma}\Big)\cdot\frac1{\epsilon_P}\Big),$$
--   then $\mathbb E\big[P(w^{(T)})-D(\alpha^{(T)})\big]\le\epsilon_P$.
--   2. **(Averaging option.)** If $T>T_0$ and
--   $$T_0\ \ge\ \Big(n+\frac1{\lambda\gamma}\Big)\log\Big(\Big(n+\frac1{\lambda\gamma}\Big)\cdot\frac1{(T-T_0)\epsilon_P}\Big),$$
--   then the output $\bar\alpha=\frac1{T-T_0}\sum_{t=T_0+1}^{T}\alpha^{(t-1)}$, $\bar w=w(\bar\alpha)$, satisfies $\mathbb E[P(\bar w)-D(\bar\alpha)]\le\epsilon_P$.
--   3. **(Random option.)** Under the same condition, if $(\bar w,\bar\alpha)=(w^{(t-1)},\alpha^{(t-1)})$ for $t$ drawn uniformly from $\{T_0+1,\dots,T\}$ independently of the run, then $\mathbb E[P(\bar w)-D(\bar\alpha)]\le\epsilon_P$.
--
--   This is the paper's main result: for smooth losses SDCA converges linearly in the duality gap, with $\tilde O\big((n+\frac1{\lambda\gamma})\log\frac1{\epsilon_P}\big)$ iterations, and the duality gap certifies primal sub-optimality.
--
--   **Formalization Note** Expectations are uniform averages over the $n^T$ coordinate sequences (`SAGA.Convex.expectIdx`). The step is any map satisfying the argmax predicate `IsSDCAStep`. $D$ is `EReal`-valued; its values are converted to reals only under the first conjunct, which asserts their finiteness. The Random option is stated over the iterates $\alpha^{(T_0)},\dots,\alpha^{(T-1)}$, which is what the proof bounds (the procedure's line "$\bar\alpha=\alpha^{(t)}$ for random $t\in T_0+1,\dots,T$" is off by one against it). $\log$ is the natural logarithm; no sign condition on it is assumed. No dual optimum $\alpha^*$ is assumed.
-- source:
--   Shalev-Shwartz and Zhang, Stochastic Dual Coordinate Ascent Methods for Regularized Loss Minimization, arXiv:1209.1873v2, §3, p. 6, Theorem 2 (Procedure SDCA and standing assumptions, p. 5)

import Mathlib
import Definitions.Def_SDCA_Smooth_Model

namespace SDCA.Smooth

/-- Theorem 2, p. 6 (Shalev-Shwartz–Zhang, arXiv:1209.1873v2). Run Procedure SDCA from `α⁽⁰⁾ = 0`
with convex `(1/γ)`-smooth losses `φᵢ` and the standing assumptions `‖xᵢ‖ ≤ 1`, `φᵢ ≥ 0`,
`φᵢ(0) ≤ 1` (p. 5), coordinates drawn i.i.d. uniformly. Let `εP > 0`. Then every dual value along
the run and at the outputs is finite, and:
1. if `T ≥ (n + 1/(λγ)) log((n + 1/(λγ)) · 1/εP)`, then `E[P(w⁽ᵀ⁾) − D(α⁽ᵀ⁾)] ≤ εP`;
2. if `T > T₀` and `T₀ ≥ (n + 1/(λγ)) log((n + 1/(λγ)) · 1/((T − T₀) εP))`, then the Averaging
   option output `ᾱ = (1/(T − T₀)) ∑_{t=T₀+1}^{T} α⁽ᵗ⁻¹⁾`, `w̄ = w(ᾱ)`, has `E[P(w̄) − D(ᾱ)] ≤ εP`;
3. under the same condition, the Random option output (the iterate `α⁽ᵗ⁻¹⁾` for `t` uniform on
   `{T₀+1, …, T}`, independent of the run) has `E[P(w̄) − D(ᾱ)] ≤ εP`. -/
theorem theorem_2 {d n : ℕ} (hn : 0 < n) (x : Fin n → EuclideanSpace ℝ (Fin d))
    (φ φ' : Fin n → ℝ → ℝ) (hconv : ∀ i, ConvexOn ℝ Set.univ (φ i))
    (lam γ : ℝ) (hlam : 0 < lam) (hγ : 0 < γ)
    (hderiv : ∀ i a, HasDerivAt (φ i) (φ' i a) a)
    (hsmooth : ∀ i a b, |φ' i a - φ' i b| ≤ (1 / γ) * |a - b|)
    (hx : ∀ i, ‖x i‖ ≤ 1) (hφnn : ∀ i a, 0 ≤ φ i a) (hφ0 : ∀ i, φ i 0 ≤ 1)
    (Δ : (Fin n → ℝ) → Fin n → ℝ) (hΔ : IsSDCAStep lam x φ Δ)
    (εP : ℝ) (hεP : 0 < εP) :
    ((∀ (T : ℕ) (js : Fin T → Fin n) (t : ℕ), dual lam x φ (alphaIter Δ js t) ≠ ⊥) ∧
      ∀ (T : ℕ) (js : Fin T → Fin n) (T₀ : ℕ), T₀ < T → dual lam x φ (alphaAvg Δ js T₀) ≠ ⊥) ∧
    (∀ T : ℕ,
      (n + 1 / (lam * γ)) * Real.log ((n + 1 / (lam * γ)) * (1 / εP)) ≤ T →
      SAGA.Convex.expectIdx n T (fun js =>
          primal lam x φ (wOf lam x (alphaIter Δ js T)) -
            (dual lam x φ (alphaIter Δ js T)).toReal) ≤ εP) ∧
    (∀ T₀ T : ℕ, T₀ < T →
      (n + 1 / (lam * γ)) * Real.log ((n + 1 / (lam * γ)) * (1 / (((T : ℝ) - T₀) * εP))) ≤ T₀ →
      SAGA.Convex.expectIdx n T (fun js =>
          primal lam x φ (wOf lam x (alphaAvg Δ js T₀)) -
            (dual lam x φ (alphaAvg Δ js T₀)).toReal) ≤ εP) ∧
    (∀ T₀ T : ℕ, T₀ < T →
      (n + 1 / (lam * γ)) * Real.log ((n + 1 / (lam * γ)) * (1 / (((T : ℝ) - T₀) * εP))) ≤ T₀ →
      (1 / ((T : ℝ) - T₀)) * ∑ t ∈ Finset.Ico T₀ T,
          SAGA.Convex.expectIdx n T (fun js =>
            primal lam x φ (wOf lam x (alphaIter Δ js t)) -
              (dual lam x φ (alphaIter Δ js t)).toReal) ≤ εP) := by sorry

end SDCA.Smooth
