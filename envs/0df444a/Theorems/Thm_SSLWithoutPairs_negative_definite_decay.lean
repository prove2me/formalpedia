-- Prove2me | Theorems.Thm_SSLWithoutPairs_negative_definite_decay
-- name    : SSLWithoutPairs.negative_definite_decay
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T06:38:40.408697+00:00
-- url     : https://prove2.me/theorems/3cee140f-f50c-4407-8e36-de62c3be341a
-- title:
--   Lemma 2: dynamics of a negative definite system
-- statement:
--   Let $H(t)$, $t\ge0$, be $d\times d$ symmetric positive definite matrices whose minimal eigenvalues are bounded away from $0$: $\lambda_{\min}(H(t))\ge\lambda_0>0$ for all $t\ge0$. If $w(t)\in\mathbb R^d$ solves
--
--   $$\frac{\mathrm d w(t)}{\mathrm dt}=-H(t)\,w(t),\qquad t\ge0,$$
--
--   then $\|w(t)\|_2\le e^{-\lambda_0t}\|w(0)\|_2$ for all $t\ge0$, and in particular $w(t)\to0$.
--
--   This lemma is used in the proofs of Theorems 2 and 3.
--
--   **Formalization Note** "Positive definite" is read as symmetric positive definite (Mathlib's `PosDef`). The paper's proof uses an orthonormal eigenbasis of $H(t)$, and the bound fails for non-symmetric $H$ (see REPORT.md).
-- source:
--   Tian, Chen and Ganguli, Understanding Self-Supervised Learning Dynamics without Contrastive Pairs, arXiv:2102.06810v4 (2021), Appendix A, Lemma 2, eqs. (47)-(50), p. 14

import Mathlib
import Definitions.Def_SSLWithoutPairs_Basic

open MeasureTheory ProbabilityTheory Filter Topology Matrix

namespace SSLWithoutPairs

theorem negative_definite_decay {d : ℕ} (H : ℝ → Matrix (Fin d) (Fin d) ℝ)
    (hH : ∀ t : ℝ, 0 ≤ t → (H t).PosDef) (lam0 : ℝ) (hlam0 : 0 < lam0)
    (hmin : ∀ t : ℝ, 0 ≤ t → lam0 ≤ minEig (H t)) (w : ℝ → Fin d → ℝ)
    (hw : ∀ t : ℝ, 0 ≤ t → ∀ i,
      HasDerivWithinAt (fun s => w s i) (-(H t *ᵥ w t) i) (Set.Ici 0) t) :
    (∀ t : ℝ, 0 ≤ t → l2Norm (w t) ≤ Real.exp (-lam0 * t) * l2Norm (w 0)) ∧
      Tendsto w atTop (𝓝 0) := by sorry

end SSLWithoutPairs
