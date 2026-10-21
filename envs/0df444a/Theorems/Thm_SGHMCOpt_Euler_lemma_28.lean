-- Prove2me | Theorems.Thm_SGHMCOpt_Euler_lemma_28
-- name    : SGHMCOpt.Euler.lemma_28
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:41:12.647663+00:00
-- url     : https://prove2.me/theorems/c3a496c0-7986-4238-806c-3ccdc18c1f79
-- title:
--   Lemma 28, p. 70 — Gibbs concentration: ∫F_z dπ_z − min F_z ≤ (d/2β) log((eM/m)(bβ/d + 1))
-- statement:
--   Under parts (i)–(iii) of Assumption 1, with $d\ge1$, $n\ge1$ and $\beta>0$, for every dataset $z\in\mathcal Z^n$ the Gibbs law $\pi_z$ of (1.7) satisfies
--   $$\int F_z(x)\,\pi_z(dx,dv)-\min_{x\in\mathbb R^d}F_z(x)\le\frac d{2\beta}\log\Big(\frac{eM}m\Big(\frac{b\beta}d+1\Big)\Big)=\mathcal J_2.$$
--
--   The $x$-marginal of $\pi_z$ concentrates near the global minimisers of the empirical risk as $\beta\to\infty$; this lemma quantifies it for finite $\beta$ (Raginsky–Rakhlin–Telgarsky 2017, Proposition 11).
--
--   **Formalization Note** The minimum is written as the infimum of $F_z\ge0$, which is attained under Assumption 1. Integrability of $F_z(x)$ under $\pi_z$ is part of the conclusion. The paper notes that the assumption $\beta\ge2/m$ of the cited proposition is not used, and states the lemma without it; so does this statement.
-- source:
--   arXiv:1809.04618v4, Lemma 28, p. 70; (3.5), p. 11 (citing Raginsky, Rakhlin, Telgarsky 2017, Proposition 11)

import Mathlib
import Definitions.Def_SGHMCOpt_Euler_Constants
import Definitions.Def_SGHMCOpt_Euler_Model

open MeasureTheory

namespace SGHMCOpt.Euler

/-- Lemma 28, p. 70 (RRT17, Proposition 11): for every dataset `z`,
`∫ F_z(x) π_z(dx, dv) − min_x F_z(x) ≤ (d/(2β)) log((eM/m)(bβ/d + 1))`. -/
theorem lemma_28 {d n : ℕ} {𝒵 : Type*} [MeasurableSpace 𝒵] (f : E d → 𝒵 → ℝ) (p : Params)
    (hd : 0 < d) (hn : 0 < n) (hloss : LossAssumption f p) (hβ : 0 < p.β) (z : Fin n → 𝒵) :
    Integrable (fun q : E d × E d => Fz f z q.1) (gibbs p f z) ∧
      ∫ q, Fz f z q.1 ∂(gibbs p f z) - ⨅ x, Fz f z x ≤ J2 p d := by sorry

end SGHMCOpt.Euler
