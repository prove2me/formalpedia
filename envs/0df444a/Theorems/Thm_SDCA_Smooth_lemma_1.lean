-- Prove2me | Theorems.Thm_SDCA_Smooth_lemma_1
-- name    : SDCA.Smooth.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T18:08:54.995974+00:00
-- url     : https://prove2.me/theorems/a4c03ab4-5987-4337-b921-3b899571c869
-- title:
--   Lemma 1 — the expected dual increase of one SDCA step is at least $s/n$ times the duality gap, minus a variance term
-- statement:
--   Let $x_1,\dots,x_n\in\mathbb R^d$ with $n\ge1$, convex losses $\varphi_1,\dots,\varphi_n$, and $\lambda>0$. Assume every conjugate $\varphi_i^*$ is $\gamma$-strongly convex for some $\gamma\ge0$ ($\gamma=0$ is allowed). Let $\Delta$ be an SDCA step, and for every $i$ and $a\in\mathbb R$ let $u_i(a)$ be a number with $-u_i(a)\in\partial\varphi_i(a)$.
--
--   Let $\alpha\in\mathbb R^n$ be a dual-feasible point ($\varphi_i^*(-\alpha_i)<+\infty$ for all $i$), $w=w(\alpha)$, and let one SDCA iteration from $\alpha$ pick the coordinate $i$ uniformly from $\{1,\dots,n\}$ and move to $\alpha^+=\alpha+\Delta(\alpha,i)e_i$. Then every $D(\alpha+\Delta(\alpha,i)e_i)$ is finite and, for every $s\in(0,1]$,
--   $$\mathbb E_i\big[D(\alpha^+)\big]-D(\alpha)\ \ge\ \frac sn\big(P(w)-D(\alpha)\big)-\Big(\frac sn\Big)^2\frac{G}{2\lambda},\qquad G=\frac1n\sum_{i=1}^n\Big(\|x_i\|^2-\frac{\gamma(1-s)\lambda n}{s}\Big)\big(u_i(w^\top x_i)-\alpha_i\big)^2 .$$
--
--   This is the key estimate of the paper: the expected increase of the dual objective in one step is bounded below by a fraction of the duality gap. With $\alpha=\alpha^{(t-1)}$ and an outer expectation over the history it is the paper's Lemma 1.
--
--   **Formalization Note** The statement is the one-step (conditional) form: it holds at every feasible dual point, and averaging over the history gives the printed form with $\mathbb E[\cdot]$ over the run. $\mathbb E_i$ is $\frac1n\sum_i$. Dual values are `EReal` and are converted to reals only where finite (the input point by feasibility, the updated points by the first conjunct). The range $s\in(0,1]$ excludes $s=0$, where $G$ divides by $s$. $-u\in\partial\varphi_i(a)$ is the subgradient inequality.
-- source:
--   Shalev-Shwartz and Zhang, Stochastic Dual Coordinate Ascent Methods for Regularized Loss Minimization, arXiv:1209.1873v2, §7.1, p. 12, Lemma 1

import Mathlib
import Definitions.Def_SDCA_Smooth_Model
open scoped InnerProductSpace

namespace SDCA.Smooth

/-- Lemma 1, p. 12 (Shalev-Shwartz–Zhang, arXiv:1209.1873v2), in conditional one-step form.
Assume every `φᵢ*` is `γ`-strongly convex (`γ ≥ 0`), `Δ` is an SDCA step, and `u i a` is a choice
with `−u i a ∈ ∂φᵢ(a)`. Then at every dual-feasible point `α` (all `φᵢ*(−αᵢ) < ∞`), for a coordinate
`i` drawn uniformly from `{1, …, n}` and every `s ∈ (0, 1]`:
the updated dual values are finite, and
`E_i[D(α + Δαᵢ eᵢ)] − D(α) ≥ (s/n)(P(w(α)) − D(α)) − (s/n)² G/(2λ)`, where
`G = (1/n) ∑ᵢ (‖xᵢ‖² − γ(1 − s)λn/s) (uᵢ − αᵢ)²` and `uᵢ = u i (w(α)ᵀ xᵢ)`. -/
theorem lemma_1 {d n : ℕ} (hn : 0 < n) (x : Fin n → EuclideanSpace ℝ (Fin d))
    (φ : Fin n → ℝ → ℝ) (hconv : ∀ i, ConvexOn ℝ Set.univ (φ i))
    (lam : ℝ) (hlam : 0 < lam)
    (γ : ℝ) (hγ : 0 ≤ γ) (hsc : ∀ i, ConjStronglyConvex (φ i) γ)
    (Δ : (Fin n → ℝ) → Fin n → ℝ) (hΔ : IsSDCAStep lam x φ Δ)
    (u : Fin n → ℝ → ℝ) (hu : ∀ i a z, φ i a + (-(u i a)) * (z - a) ≤ φ i z)
    (α : Fin n → ℝ) (hfeas : ∀ i, SDCA.Lipschitz.conj (φ i) (-α i) ≠ ⊤)
    (s : ℝ) (hs0 : 0 < s) (hs1 : s ≤ 1) :
    (∀ i, dual lam x φ (SDCA.Lipschitz.sdcaStep Δ α i) ≠ ⊥) ∧
    (1 / (n : ℝ)) * ∑ i, (dual lam x φ (SDCA.Lipschitz.sdcaStep Δ α i)).toReal - (dual lam x φ α).toReal ≥
      s / n * (primal lam x φ (wOf lam x α) - (dual lam x φ α).toReal) -
        (s / n) ^ 2 *
          ((1 / (n : ℝ)) * ∑ i, (‖x i‖ ^ 2 - γ * (1 - s) * lam * n / s) *
            (u i ⟪wOf lam x α, x i⟫_ℝ - α i) ^ 2) / (2 * lam) := by sorry

end SDCA.Smooth
