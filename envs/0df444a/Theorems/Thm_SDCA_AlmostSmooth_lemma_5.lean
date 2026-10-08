-- Prove2me | Theorems.Thm_SDCA_AlmostSmooth_lemma_5
-- name    : SDCA.AlmostSmooth.lemma_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T19:06:30.663685+00:00
-- url     : https://prove2.me/theorems/ca856510-9352-4a07-bf4a-dd03488001c4
-- title:
--   Lemma 5 — under (5), one SDCA step increases the dual by $\frac{s}{2n}$ of the dual sub-optimality, minus a variance term
-- statement:
--   Consider Procedure SDCA for problem (1) with $\lambda>0$, and suppose the dual strong convexity inequality (5) holds at $\alpha^*$ with constants $\gamma_1,\dots,\gamma_n$ and $w^*=w(\alpha^*)$. Let $\alpha$ be any feasible dual point (the state $\alpha^{(t-1)}$), and let the next state be $\alpha^{(t)}=\alpha+\Delta\alpha_i e_i$ with $i$ uniform on $\{1,\dots,n\}$ and $\Delta\alpha_i$ an SDCA step. Then for every $s\in(0,1]$,
--   $$
--   \mathbb E\bigl[D(\alpha^{(t)})\bigr]-D(\alpha)\ge\frac{s}{2n}\bigl(D(\alpha^*)-D(\alpha)\bigr)+\frac{3s\lambda}{4n}\|w^*-w(\alpha)\|^2-\Bigl(\frac sn\Bigr)^2\frac{G_*(s)}{2\lambda},
--   $$
--   where
--   $$
--   G_*(s)=\frac1n\sum_{i=1}^n\Bigl(\|x_i\|^2-\frac{\gamma_i\lambda n}{s}\Bigr)(\alpha_i^*-\alpha_i)^2 .
--   $$
--   Moreover every possible next state is feasible.
--
--   This is the one-step progress estimate behind the linear rate of Theorem 5; Lemma 6 bounds $G_*(s)$.
--
--   **Formalization Note** The statement is conditional on the current state: the expectation is the average $\frac1n\sum_i D(\alpha+\Delta\alpha_i e_i)$ over the coordinate. Averaging it over the history gives the paper's form $\mathbb E[D(\alpha^{(t)})-D(\alpha^{(t-1)})]\ge\dots$ with $\mathbb E[(\alpha_i^*-\alpha_i^{(t-1)})^2]$ in $G_*^{(t)}(s)$; the printed $\|w^*-w^{(t-1)}\|^2$ without expectation is the conditional quantity. The range $s\in(0,1]$ excludes $s=0$, where $\gamma_i\lambda n/s$ is undefined. Dual values are converted to reals only after their finiteness is part of the statement.
-- source:
--   Shalev-Shwartz and Zhang, Stochastic Dual Coordinate Ascent Methods for Regularized Loss Minimization, arXiv:1209.1873v2, p. 19, Lemma 5 (proof pp. 19–20)

import Mathlib
import Definitions.Def_SDCA_AlmostSmooth_Model

namespace SDCA.AlmostSmooth

/-- Lemma 5 (p. 19), in conditional (one-step) form: if (5) holds, then for every feasible dual
point `α` (the state `α⁽ᵗ⁻¹⁾`) and every `s ∈ (0, 1]`, the SDCA step on a uniformly random
coordinate satisfies
`E[D(α⁽ᵗ⁾)] − D(α) ≥ s/(2n)(D(α*) − D(α)) + 3sλ/(4n)‖w* − w(α)‖² − (s/n)² G*(s)/(2λ)`, with
`G*(s) = (1/n) ∑ᵢ (‖xᵢ‖² − γᵢλn/s)(α*ᵢ − αᵢ)²` and `w* = w(α*)`. The new dual values are finite. -/
theorem lemma_5 {d n : ℕ} (hn : 0 < n) (x : Fin n → EuclideanSpace ℝ (Fin d))
    (φ : Fin n → ℝ → ℝ) (lam : ℝ) (hlam : 0 < lam) (Δ : (Fin n → ℝ) → Fin n → ℝ)
    (hΔ : SDCA.Smooth.IsSDCAStep lam x φ Δ) (γ : Fin n → ℝ) (αstar : Fin n → ℝ)
    (h5 : DualStrongConvexity lam x φ γ αstar) (α : Fin n → ℝ) (hα : Feasible φ α)
    (s : ℝ) (hs0 : 0 < s) (hs1 : s ≤ 1) :
    (∀ i, SDCA.Smooth.dual lam x φ (SDCA.Lipschitz.sdcaStep Δ α i) ≠ ⊥) ∧
      s / (2 * n) * ((SDCA.Smooth.dual lam x φ αstar).toReal - (SDCA.Smooth.dual lam x φ α).toReal) +
          3 * s * lam / (4 * n) * ‖SDCA.Smooth.wOf lam x αstar - SDCA.Smooth.wOf lam x α‖ ^ 2 -
          (s / n) ^ 2 *
            ((1 / (n : ℝ)) * ∑ i, (‖x i‖ ^ 2 - γ i * lam * n / s) * (αstar i - α i) ^ 2) /
            (2 * lam) ≤
        (1 / (n : ℝ)) * ∑ i, (SDCA.Smooth.dual lam x φ (SDCA.Lipschitz.sdcaStep Δ α i)).toReal -
          (SDCA.Smooth.dual lam x φ α).toReal := by sorry

end SDCA.AlmostSmooth
