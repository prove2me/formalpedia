-- Prove2me | Theorems.Thm_TensorNP_SpectralNorm_display_22
-- name    : TensorNP.SpectralNorm.display_22
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T17:08:05.22085+00:00
-- url     : https://prove2.me/theorems/f7f17c6c-b774-4bc8-bb5b-11e0abb441f6
-- title:
--   §6, display before (22) and (22) — M_l = 1 + (ω − l)/(lω); M_ω = 1, M_l > 1 for l < ω, M_l < 1 for l > ω
-- statement:
--   Let $G$ be a simple graph on $v\ge1$ vertices with clique number $\omega$, let $l$ be a positive integer, $Q_l=A_G+\frac1lJ$, and $M_l=\max_{\mathbf x\in\Delta_v}\mathbf x^\top Q_l\mathbf x$. Then the maximum is attained and
--   $$
--   M_l = 1+\frac{\omega-l}{l\,\omega}.
--   $$
--   Consequently $M_\omega=1$, and
--   $$
--   M_l>1 \ \text{ if } l<\omega,\qquad M_l<1\ \text{ if } l>\omega. \tag{22}
--   $$
--
--   This translates the Motzkin–Straus theorem into a family of quadratic programs, indexed by $l$, whose optimal value crosses $1$ exactly at $l=\omega$.
--
--   **Formalization Note** The first clause is `IsGreatest` of the image of the simplex under $\mathbf x\mapsto\mathbf x^\top Q_l\mathbf x$ with value $1+(\omega-l)/(l\omega)$; the second says that the `sSup`-based definition `Mval G l` has this value. Hypotheses $v\ge1$ and $l\ge1$ are the paper's standing ones ($l$ is a "positive integer", and $\omega\ge1$ requires a nonempty vertex set).
-- source:
--   Hillar & Lim, Most Tensor Problems Are NP-Hard, J. ACM 60(6) (2013), Art. 45 (final version, arXiv:0911.1393v5), p. 0:22, display defining M_l and (22)

import Mathlib
import Definitions.Def_TensorNP_SpectralNorm_Tensor
import Definitions.Def_TensorNP_SpectralNorm_CliqueTensor

namespace TensorNP.SpectralNorm

open Matrix

/-- **The value of `M_l` and (22)** (p. 0:22). For a simple graph `G` on `v ≥ 1` vertices with
clique number `ω` and a positive integer `l`, the maximum of `xᵀ Q_l x` over `Δ_v` is
`1 + (ω − l)/(lω)`; hence `M_ω = 1`, `M_l > 1` if `l < ω`, and `M_l < 1` if `l > ω`. -/
theorem display_22 {v : ℕ} (hv : 0 < v) (G : SimpleGraph (Fin v)) [DecidableRel G.Adj]
    (l : ℕ) (hl : 1 ≤ l) :
    IsGreatest ((fun x : Fin v → ℝ => x ⬝ᵥ (Qmat G l *ᵥ x)) '' stdSimplex ℝ (Fin v))
        (1 + ((G.cliqueNum : ℝ) - l) / ((l : ℝ) * G.cliqueNum)) ∧
      Mval G l = 1 + ((G.cliqueNum : ℝ) - l) / ((l : ℝ) * G.cliqueNum) ∧
      (l = G.cliqueNum → Mval G l = 1) ∧
      (l < G.cliqueNum → 1 < Mval G l) ∧
      (G.cliqueNum < l → Mval G l < 1) := by sorry

end TensorNP.SpectralNorm
