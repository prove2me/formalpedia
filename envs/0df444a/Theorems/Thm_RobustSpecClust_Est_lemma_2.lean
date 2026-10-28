-- Prove2me | Theorems.Thm_RobustSpecClust_Est_lemma_2
-- name    : RobustSpecClust.Est.lemma_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-16T09:43:23.91499+00:00
-- url     : https://prove2.me/theorems/d0fc2bff-5f11-4f0e-93d1-76fa488ecf81
-- title:
--   Lemma 2, pp. 12–13 — ‖X̂_I − X⁰_I‖₁ ≤ ⟨R − γE_N, X⁰ − X̂⟩ / min(R^in_min − γ, γ − R^out_max), and the υ-form
-- statement:
--   Let $R$ be the reference matrix (6) built from $K$, $\varphi$, $\tau_{\mathrm{in}}$, $\tau^{(k,l)}_{\mathrm{out}}$ and $\gamma$ ($r \ge 2$ clusters), $X^0$ the true clustering matrix, and $\hat X$ any matrix with entries in $[0,1]$. Write $\|\cdot\|_1$ for the entrywise $\ell_1$ norm and $A_{\mathcal I}$ for the inlier block.
--
--   1. If $a, b$ are reals with $R_{ij} \ge a$ for all same-cluster inlier pairs, $R_{ij} \le b$ for all different-cluster inlier pairs, and $b < \gamma < a$, then
--   $$\|\hat X_{\mathcal I} - X^0_{\mathcal I}\|_1 \le \frac{\langle R - \gamma E_N, X^0 - \hat X\rangle}{\min(a - \gamma, \gamma - b)} .$$
--   2. If $\tau_{\mathrm{out}} = \max_{k\ne l} \tau^{(k,l)}_{\mathrm{out}} < \tau_{\mathrm{in}}$ and $\gamma = \upsilon\tau_{\mathrm{in}} + (1-\upsilon)\tau_{\mathrm{out}}$ for some $\upsilon \in (0,1)$, then
--   $$\|\hat X_{\mathcal I} - X^0_{\mathcal I}\|_1 \le \frac{\langle R - \gamma E_N, X^0 - \hat X\rangle}{\min\{\upsilon, 1-\upsilon\}(\tau_{\mathrm{in}} - \tau_{\mathrm{out}})} .$$
--
--   With $a = R^{\mathrm{in}}_{\min}$ and $b = R^{\mathrm{out}}_{\max}$, part 1 is the paper's first bound. Lemma 2 converts the suboptimality of $\hat X$ in the reference problem into an $\ell_1$ estimation error on the inliers.
--
--   **Formalization Note** The statement is slightly more general than the page: $\hat X$ is any matrix in the box (the proof in Appendix C uses only feasibility), and $R^{\mathrm{in}}_{\min}$, $R^{\mathrm{out}}_{\max}$ may be replaced by any lower/upper bounds $a$, $b$. Part 2 carries the standing requirement $\tau_{\mathrm{in}} > \tau_{\mathrm{out}}$ of p. 12 (without it the denominator is non-positive); under it, $R^{\mathrm{out}}_{\max} < \gamma < R^{\mathrm{in}}_{\min}$ holds automatically because $R^{\mathrm{in}}_{\min} \ge \tau_{\mathrm{in}}$ and $R^{\mathrm{out}}_{\max} \le \tau_{\mathrm{out}}$.
-- source:
--   arXiv:1912.07546v3, Lemma 2, pp. 12–13; proof in Appendix C, p. 38

import Mathlib
import Definitions.Def_RobustSpecClust_Est_Setting
open MeasureTheory ProbabilityTheory

namespace RobustSpecClust.Est

theorem lemma_2 {n m r : ℕ} (hr : 2 ≤ r) (K : Matrix (Pt n m) (Pt n m) ℝ) (φ : Fin n → Fin r)
    (τin : ℝ) (τout : Fin r → Fin r → ℝ) (γ : ℝ) (Xh : Matrix (Pt n m) (Pt n m) ℝ)
    (hXh : ∀ i j, 0 ≤ Xh i j ∧ Xh i j ≤ 1) :
    (∀ a b : ℝ,
      (∀ i j, φ i = φ j → a ≤ refMatrix K φ τin τout γ (Sum.inl i) (Sum.inl j)) →
      (∀ i j, φ i ≠ φ j → refMatrix K φ τin τout γ (Sum.inl i) (Sum.inl j) ≤ b) →
      b < γ → γ < a →
      l1 (inlierBlock Xh - inlierBlock (trueClust (m := m) φ)) ≤
        frobInner (refMatrix K φ τin τout γ - γ • ones (Pt n m)) (trueClust φ - Xh) /
          min (a - γ) (γ - b)) ∧
    (∀ υ : ℝ, 0 < υ → υ < 1 → tauOutMax τout hr < τin →
      γ = υ * τin + (1 - υ) * tauOutMax τout hr →
      l1 (inlierBlock Xh - inlierBlock (trueClust (m := m) φ)) ≤
        frobInner (refMatrix K φ τin τout γ - γ • ones (Pt n m)) (trueClust φ - Xh) /
          (min υ (1 - υ) * (τin - tauOutMax τout hr))) := by sorry

end RobustSpecClust.Est
