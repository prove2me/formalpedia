-- Prove2me | Theorems.Thm_SDCA_Lipschitz_lemma_1
-- name    : SDCA.Lipschitz.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T17:11:39.401971+00:00
-- url     : https://prove2.me/theorems/c40ed995-ae7f-455f-8e6e-4b85e3da69cb
-- title:
--   Lemma 1, p. 12 — the expected dual increase of an SDCA step is at least $\frac sn$ times the duality gap minus $(\frac sn)^2\frac{G}{2\lambda}$
-- statement:
--   Throughout, $x_1,\dots,x_n\in\mathbb R^d$ ($n\ge1$), $\phi_1,\dots,\phi_n:\mathbb R\to\mathbb R$ are convex, $\lambda>0$, $P$ is the primal objective (1), $D$ the dual objective (2), $\phi_i^*$ the convex conjugate and $w(\alpha)=\frac1{\lambda n}\sum_i\alpha_ix_i$.
--
--   Let $\gamma\ge0$ and assume every $\phi_i^*$ is $\gamma$-strongly convex (the p. 2 display; $\gamma=0$ is allowed). Let $\Delta$ be an SDCA step rule, let $u_i(\cdot)$ be a sub-gradient selection, $-u_i(a)\in\partial\phi_i(a)$ for all $i,a$, and let $0<s\le1$. Let $\alpha=\alpha^{(t-1)}$ be any dual-feasible state ($\phi_j^*(-\alpha_j)<\infty$ for all $j$), $w=w(\alpha)$, $u_i=u_i(x_i^\top w)$, and let $\alpha^{(t)}=\alpha+\Delta(\alpha,i)e_i$ with $i$ uniform on $\{1,\dots,n\}$. Then all the dual values involved are finite and
--   $$\mathbb E_i\bigl[D(\alpha^{(t)})\bigr]-D(\alpha)\ \ge\ \frac sn\bigl(P(w)-D(\alpha)\bigr)-\Bigl(\frac sn\Bigr)^2\frac{G}{2\lambda},\qquad G=\frac1n\sum_{i=1}^n\Bigl(\|x_i\|^2-\frac{\gamma(1-s)\lambda n}{s}\Bigr)(u_i-\alpha_i)^2 .$$
--
--   This is the key lemma of the paper: the expected dual increase of one SDCA iteration is controlled from below by the current duality gap, which gives a recursion for the dual sub-optimality.
--
--   **Formalization Note** The paper states the lemma with expectations over the whole history; this is the conditional (one-step) form for a fixed state $\alpha^{(t-1)}$, from which the printed form follows by averaging over the history. $\mathbb E_i$ is the average $\frac1n\sum_i$. The paper allows $s\in[0,1]$; $G$ divides by $s$, so $s>0$ is assumed. The dual values are converted to reals only after their finiteness is asserted in the conclusion.
-- source:
--   Shalev-Shwartz and Zhang, Stochastic Dual Coordinate Ascent Methods for Regularized Loss Minimization, arXiv:1209.1873v2, §7.1, p. 12, Lemma 1

import Mathlib
import Definitions.Def_SDCA_Lipschitz_Model

namespace SDCA.Lipschitz

/-- Lemma 1, p. 12, in conditional (one-step) form. Assume every `φᵢ*` is `γ`-strongly convex
(`γ ≥ 0`; `γ = 0` is allowed), let `0 < s ≤ 1`, let `u` be a sub-gradient selection
(`−u i a ∈ ∂φᵢ(a)`), and let `α = α⁽ᵗ⁻¹⁾` be any dual-feasible state. Averaging over the uniformly
picked coordinate `i` (so that `α⁽ᵗ⁾ = α + Δαᵢeᵢ`),
`E[D(α⁽ᵗ⁾)] − D(α) ≥ (s/n)(P(w(α)) − D(α)) − (s/n)² G/(2λ)`, with
`G = (1/n) ∑ᵢ (‖xᵢ‖² − γ(1−s)λn/s)(uᵢ − αᵢ)²` and `uᵢ = u i (xᵢᵀw(α))`.
All dual values involved are finite. -/
theorem lemma_1 {d n : ℕ} (φ : Fin n → ℝ → ℝ) (x : Fin n → EuclideanSpace ℝ (Fin d)) (lam : ℝ)
    (hn : 0 < n) (hlam : 0 < lam) (hconv : ∀ i, ConvexOn ℝ Set.univ (φ i))
    (Δ : (Fin n → ℝ) → Fin n → ℝ) (hΔ : IsSDCAStep φ x lam Δ)
    (γ : ℝ) (hγ : 0 ≤ γ)
    (hsc : ∀ (i : Fin n) (u v r : ℝ), 0 ≤ r → r ≤ 1 →
      conj (φ i) (r * u + (1 - r) * v) ≤
        ((r : ℝ) : EReal) * conj (φ i) u + ((1 - r : ℝ) : EReal) * conj (φ i) v
          - ((γ * r * (1 - r) / 2 * (u - v) ^ 2 : ℝ) : EReal))
    (s : ℝ) (hs0 : 0 < s) (hs1 : s ≤ 1)
    (u : Fin n → ℝ → ℝ) (hu : ∀ i a, -(u i a) ∈ subdiff (φ i) a)
    (α : Fin n → ℝ) (hα : ∀ j, conj (φ j) (-α j) ≠ ⊤) :
    dual φ x lam α ≠ ⊥ ∧ (∀ i, dual φ x lam (sdcaStep Δ α i) ≠ ⊥) ∧
      (1 / (n : ℝ)) * ∑ i, (dual φ x lam (sdcaStep Δ α i)).toReal - (dual φ x lam α).toReal ≥
        s / n * (primal φ x lam (wOf x lam α) - (dual φ x lam α).toReal)
          - (s / n) ^ 2 *
            ((1 / (n : ℝ)) * ∑ i, (‖x i‖ ^ 2 - γ * (1 - s) * lam * n / s)
                * (u i (inner ℝ (wOf x lam α) (x i)) - α i) ^ 2) / (2 * lam) := by sorry

end SDCA.Lipschitz
