-- Prove2me | Theorems.Thm_SSLWithoutPairs_eigenspace_alignment
-- name    : SSLWithoutPairs.eigenspace_alignment
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T06:40:20.2667+00:00
-- url     : https://prove2.me/theorems/0033fa0e-6c1e-4db1-9e3f-62ba8bceabe5
-- title:
--   Theorem 3: eigenspace alignment
-- statement:
--   Let $\alpha_p>0$, $\eta\ge0$, $\sigma\in\mathbb R$, and let $\tau(t)$ be any real function. Let $F(t)$ (positive semidefinite) and $W_p(t)$ (symmetric), $t\ge0$, be $d\times d$ matrices solving the symmetrised dynamics (7):
--
--   $$\dot W_p=-\frac{\alpha_p}{2}(1+\sigma^2)\{W_p,F\}+\alpha_p\tau F-\eta W_p,\qquad \dot F=-(1+\sigma^2)\{W_p^2,F\}+\tau\{W_p,F\}-2\eta F.$$
--
--   Then the commutator $[F,W_p]=FW_p-W_pF$ satisfies
--
--   $$\frac{\mathrm d}{\mathrm dt}[F,W_p]=-[F,W_p]K-K[F,W_p],\qquad K(t)=(1+\sigma^2)\Big[\frac{\alpha_p}{2}F+W_p^2-\frac{\tau}{1+\sigma^2}W_p\Big]+\frac32\eta I.$$
--
--   If moreover $\inf_{t\ge0}\lambda_{\min}(K(t))\ge\lambda_0>0$, then for all $t\ge0$
--
--   $$\|[F(t),W_p(t)]\|_F\le e^{-2\lambda_0t}\,\|[F(0),W_p(0)]\|_F\to0.$$
--
--   In words, the eigenspaces of the predictor and of its input correlation matrix align.
--
--   **Formalization Note** Symmetry of $W_p(t)$ (Assumption 3) and positive semidefiniteness of $F(t)=WW^\top$ are assumed for all $t\ge0$. The paper's condition "$\inf_t\lambda_{\min}(K(t))=\lambda_0>0$" is written as "$\lambda_{\min}(K(t))\ge\lambda_0>0$ for all $t\ge0$"; the two forms are equivalent.
-- source:
--   Tian, Chen and Ganguli, Understanding Self-Supervised Learning Dynamics without Contrastive Pairs, arXiv:2102.06810v4 (2021), Section 3.1, Theorem 3, eqs. (7)-(10), p. 5; proof in Appendix B.1, Theorem 3, eqs. (67)-(75), p. 16

import Mathlib
import Definitions.Def_SSLWithoutPairs_Basic

open MeasureTheory ProbabilityTheory Filter Topology Matrix

namespace SSLWithoutPairs

theorem eigenspace_alignment {d : ℕ} (αp σ η : ℝ) (hαp : 0 < αp) (hη : 0 ≤ η) (τ : ℝ → ℝ)
    (F Wp : ℝ → Matrix (Fin d) (Fin d) ℝ)
    (hF : ∀ t : ℝ, 0 ≤ t → (F t).PosSemidef) (hWp : ∀ t : ℝ, 0 ≤ t → (Wp t)ᵀ = Wp t)
    (hdWp : HasMatDerivOn Wp (fun t => symFlowWp αp σ η (τ t) (Wp t) (F t)))
    (hdF : HasMatDerivOn F (fun t => symFlowF σ η (τ t) (Wp t) (F t))) :
    HasMatDerivOn (fun t => commutator (F t) (Wp t))
      (fun t => -(commutator (F t) (Wp t) * alignK αp σ η (τ t) (F t) (Wp t)) -
        alignK αp σ η (τ t) (F t) (Wp t) * commutator (F t) (Wp t)) ∧
    ∀ lam0 : ℝ, 0 < lam0 → (∀ t : ℝ, 0 ≤ t → lam0 ≤ minEig (alignK αp σ η (τ t) (F t) (Wp t))) →
      ∀ t : ℝ, 0 ≤ t → frobNorm (commutator (F t) (Wp t)) ≤
        Real.exp (-2 * lam0 * t) * frobNorm (commutator (F 0) (Wp 0)) := by sorry

end SSLWithoutPairs
