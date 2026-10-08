-- Prove2me | Theorems.Thm_SDCA_AlmostSmooth_dual_recursion
-- name    : SDCA.AlmostSmooth.dual_recursion
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T19:06:22.461475+00:00
-- url     : https://prove2.me/theorems/00b9ae92-0f30-4494-8f7c-13a280fa5fc7
-- title:
--   Proof of Theorem 5 (p. 20) — $\epsilon_D^{(t)}\le(1-\frac{s}{2n})\epsilon_D^{(t-1)}+(\frac sn)^2\frac{G_*(s)}{2\lambda}$ and its unrolled form
-- statement:
--   Consider Procedure SDCA started at $\alpha^{(0)}=0$, each iteration choosing its coordinate uniformly at random and independently, for problem (1) with $\lambda>0$, data $\|x_i\|\le1$, and convex, $L$-Lipschitz losses $\varphi_i\ge0$ with $\varphi_i(0)\le1$. Let $\alpha^*$ maximize the dual $D$, and suppose (5) holds at $\alpha^*$ with constants $\gamma_i\ge0$ and $w^*=w(\alpha^*)$. Let $s\in(0,1]$, put
--   $$
--   \epsilon_D^{(t)}=\mathbb E\bigl[D(\alpha^*)-D(\alpha^{(t)})\bigr],\qquad G_*(s)=\frac{4L^2N\bigl(s/(\lambda n)\bigr)}{n},\qquad N(u)=\#\{i:\gamma_i<u\}.
--   $$
--   Then $D(\alpha^*)$ and every $D(\alpha^{(t)})$ are finite, and
--
--   1. for every $t\ge1$,
--   $$
--   \epsilon_D^{(t)}\le\Bigl(1-\frac{s}{2n}\Bigr)\epsilon_D^{(t-1)}+\Bigl(\frac sn\Bigr)^2\frac{G_*(s)}{2\lambda};
--   $$
--   2. for every $t\ge0$,
--   $$
--   \epsilon_D^{(t)}\le\Bigl(1-\frac{s}{2n}\Bigr)^t\epsilon_D^{(0)}+\frac sn\cdot\frac{G_*(s)}{\lambda}.
--   $$
--
--   These are the first two displays of the proof of Theorem 5; with $\epsilon_D^{(0)}\le1$ (Lemma 2) they give the theorem.
--
--   **Formalization Note** The expectation over the first $t$ coordinate choices is the uniform average over all sequences in $\{1,\dots,n\}^t$ (`SAGA.Convex.expectIdx`). The intermediate form $\frac{1}{1-(1-s/(2n))}(\frac sn)^2\frac{G_*(s)}{2\lambda}$ of the printed chain equals $\frac sn\frac{G_*(s)}{\lambda}$ and is stated in the simplified form.
-- source:
--   Shalev-Shwartz and Zhang, Stochastic Dual Coordinate Ascent Methods for Regularized Loss Minimization, arXiv:1209.1873v2, §7.6, proof of Theorem 5, p. 20, first and second displays

import Mathlib
import Definitions.Def_SDCA_AlmostSmooth_Model
import Definitions.Def_SAGA_Convex_sagaRun

namespace SDCA.AlmostSmooth

/-- §7.6, proof of Theorem 5 (p. 20), first and second displays. Procedure SDCA with
`α⁽⁰⁾ = 0`, L-Lipschitz losses, (5), and `s ∈ (0, 1]`. With
`ϵ_D⁽ᵗ⁾ = E[D(α*) − D(α⁽ᵗ⁾)]` and `G*(s) = 4L²N(s/(λn))/n`:
`ϵ_D⁽ᵗ⁾ ≤ (1 − s/(2n)) ϵ_D⁽ᵗ⁻¹⁾ + (s/n)² G*(s)/(2λ)` for `t ≥ 1`, and
`ϵ_D⁽ᵗ⁾ ≤ (1 − s/(2n))ᵗ ϵ_D⁽⁰⁾ + (s/n) G*(s)/λ` for all `t`. All dual values involved are finite. -/
theorem dual_recursion {d n : ℕ} (hn : 0 < n) (x : Fin n → EuclideanSpace ℝ (Fin d))
    (hx : ∀ i, ‖x i‖ ≤ 1) (φ : Fin n → ℝ → ℝ) (hφconv : ∀ i, ConvexOn ℝ Set.univ (φ i))
    (hφnn : ∀ i a, 0 ≤ φ i a) (hφ0 : ∀ i, φ i 0 ≤ 1) (L : ℝ)
    (hL : ∀ i, ∀ a b : ℝ, |φ i a - φ i b| ≤ L * |a - b|) (lam : ℝ) (hlam : 0 < lam)
    (Δ : (Fin n → ℝ) → Fin n → ℝ) (hΔ : SDCA.Smooth.IsSDCAStep lam x φ Δ) (αstar : Fin n → ℝ)
    (hopt : ∀ β, SDCA.Smooth.dual lam x φ β ≤ SDCA.Smooth.dual lam x φ αstar) (γ : Fin n → ℝ) (hγ : ∀ i, 0 ≤ γ i)
    (h5 : DualStrongConvexity lam x φ γ αstar) (s : ℝ) (hs0 : 0 < s) (hs1 : s ≤ 1) :
    let Gs : ℝ := 4 * L ^ 2 * (countBelow γ (s / (lam * n)) : ℝ) / n
    let ε : ℕ → ℝ := fun t => SAGA.Convex.expectIdx n t (fun js =>
      (SDCA.Smooth.dual lam x φ αstar).toReal - (SDCA.Smooth.dual lam x φ (SDCA.Smooth.alphaIter Δ js t)).toReal)
    SDCA.Smooth.dual lam x φ αstar ≠ ⊥ ∧
      (∀ (t : ℕ) (js : Fin t → Fin n), SDCA.Smooth.dual lam x φ (SDCA.Smooth.alphaIter Δ js t) ≠ ⊥) ∧
      (∀ t : ℕ, 1 ≤ t → ε t ≤ (1 - s / (2 * n)) * ε (t - 1) + (s / n) ^ 2 * Gs / (2 * lam)) ∧
      (∀ t : ℕ, ε t ≤ (1 - s / (2 * n)) ^ t * ε 0 + (s / n) * Gs / lam) := by sorry

end SDCA.AlmostSmooth
