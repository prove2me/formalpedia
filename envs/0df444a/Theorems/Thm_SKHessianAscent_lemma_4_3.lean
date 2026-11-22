-- Prove2me | Theorems.Thm_SKHessianAscent_lemma_4_3
-- name    : SKHessianAscent.lemma_4_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-22T20:11:47.549533+00:00
-- url     : https://prove2.me/theorems/b2c97bce-23f9-4444-a487-bb5863a84bf8
-- title:
--   Lemma 4.3, desideratum (d2b) — Löwner sandwich $C_{\mathrm{TAP}}^{-1}D^{-1}(m)\preceq\widehat Q(m)\preceq c^{-1}D^{-1}(m)$ on the safe set
-- statement:
--   Fix $0<\beta<1$. There is a constant $C_{\mathrm{TAP}}=C_{\mathrm{TAP}}(\beta)\in(0,\infty)$ such that for every $n$, every symmetric $A\in\mathbb R^{n\times n}$ with $\|A\|_{\mathrm{op}}\le3$, every $c>0$ and every $m$ in the safe set $\mathcal S_{\beta,A}(c)$,
--
--   $$
--   C_{\mathrm{TAP}}^{-1}\,D^{-1}(m)\ \preceq\ \widehat Q(m)\ \preceq\ c^{-1}\,D^{-1}(m),
--   $$
--
--   where $D^{-1}(m)=\mathrm{diag}(1-m_i^2)$ and $\widehat Q(m)=(\nabla^2_m\mathcal F_{\mathrm{TAP}}(m))^{-1}$.
--
--   This gives the regularity of the inverse TAP Hessian needed for the coefficients of the algorithmic process.
--
--   **Formalization Note** The paper conditions on a "master event" on $A$; its proof uses only $\|A\|_{\mathrm{op}}\le3$ (and the symmetry of a GOE matrix), which is the hypothesis here. The upper constant is the safe-set parameter itself, written $c_{\mathrm{TAP}}(\beta,T)$ in the paper.
-- source:
--   H. Lee, J. S. Sandhu, J. Shi, Potential Hessian Ascent IV: Sampling the Sherrington–Kirkpatrick model at β < 1, https://arxiv.org/abs/2609.30590, Lemma 4.3, p. 24; desideratum (d2b), p. 5

import Mathlib
import Definitions.Def_RandMatDisc_goe
import Definitions.Def_SKHessianAscent_Model

open OAI.CriticalSK SKAnnealing.Sampling MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology BigOperators

namespace SKHessianAscent

theorem lemma_4_3 (β : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ), A.IsSymm → opNorm A ≤ 3 →
        ∀ c : ℝ, 0 < c → ∀ m ∈ safeSet β A c,
          (Qhat β A m - C⁻¹ • Dinv m).PosSemidef ∧
          (c⁻¹ • Dinv m - Qhat β A m).PosSemidef := by sorry

end SKHessianAscent
