-- Prove2me | Theorems.Thm_SSLWithoutPairs_alignment_condition_modes
-- name    : SSLWithoutPairs.alignment_condition_modes
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T06:43:09.240914+00:00
-- url     : https://prove2.me/theorems/6b494a26-e4ad-4d68-9058-13bde99d7f02
-- title:
--   Eq. (17): positive definiteness of $K(t)$ in the aligned eigenbasis
-- statement:
--   Let $\alpha_p>0$, $\eta\ge0$, and suppose the eigenspaces are aligned: $W_p=U\operatorname{diag}[p_j]U^\top$ and $F=U\operatorname{diag}[s_j]U^\top$ for an orthogonal $U$, on the invariant parabola $s_j=\alpha_p^{-1}p_j^2$. With $\Delta_j=p_j[\tau-(1+\sigma^2)p_j]-\eta$, the matrix $K$ of eq. (9) is positive definite if and only if, for every $j$,
--
--   $$\Delta_j<\tfrac12\big[\alpha_p(1+\sigma^2)s_j+\eta\big].$$
--
--   This is the second of the two criteria of Section 3.2. The first, $\Delta_j>0$, is needed for $p_j$ to grow.
--
--   **Formalization Note** The invariance $s_j=\alpha_p^{-1}p_j^2$ is kept as a hypothesis because the paper states it, although the equivalence does not use it.
-- source:
--   Tian, Chen and Ganguli, Understanding Self-Supervised Learning Dynamics without Contrastive Pairs, arXiv:2102.06810v4 (2021), Section 3.2, eq. (17), p. 7

import Mathlib
import Definitions.Def_SSLWithoutPairs_Basic

open MeasureTheory ProbabilityTheory Filter Topology Matrix

namespace SSLWithoutPairs

theorem alignment_condition_modes {d : ℕ} (αp σ η τ : ℝ) (hαp : 0 < αp) (hη : 0 ≤ η)
    (U : Matrix.orthogonalGroup (Fin d) ℝ) (p s : Fin d → ℝ) (hinv : ∀ j, s j = αp⁻¹ * p j ^ 2) :
    (alignK αp σ η τ
        ((U : Matrix (Fin d) (Fin d) ℝ) * diagonal s * (U : Matrix (Fin d) (Fin d) ℝ)ᵀ)
        ((U : Matrix (Fin d) (Fin d) ℝ) * diagonal p * (U : Matrix (Fin d) (Fin d) ℝ)ᵀ)).PosDef ↔
      ∀ j, modeDelta σ η τ (p j) < (αp * (1 + σ ^ 2) * s j + η) / 2 := by sorry

end SSLWithoutPairs
