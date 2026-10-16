-- Prove2me | Theorems.Thm_RobustSpecClust_Est_lemma_1
-- name    : RobustSpecClust.Est.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-16T09:43:27.266801+00:00
-- url     : https://prove2.me/theorems/729f7cf9-fa9f-4404-8ef1-42ef2de506ea
-- title:
--   Lemma 1, p. 12 — under (7) and R^out_max < γ < R^in_min, X⁰ maximizes the reference problem (5)
-- statement:
--   Consider $n$ inliers with labels $\varphi_i \in [r]$ and $m$ outliers, a matrix $K$ indexed by all $N = n+m$ points, thresholds $\tau_{\mathrm{in}}$ and $\tau^{(k,l)}_{\mathrm{out}}$, and $\gamma \in \mathbb R$. Let $R$ be the reference matrix (6) built from these data, and $X^0$ the true clustering matrix. Suppose that
--   1. $R_{ij} > \gamma$ for all inliers $i, j$ in the same cluster, and
--   2. $R_{ij} < \gamma$ for all inliers $i, j$ in different clusters.
--
--   Then $X^0 \in [0,1]^{N\times N}$ and, for every $X \in [0,1]^{N\times N}$,
--   $$\langle R - \gamma E_N, X\rangle \le \langle R - \gamma E_N, X^0\rangle .$$
--
--   That is, $X^0$ maximizes the reference optimization problem (5). This is the step that ties the reference problem to the ground truth in the analysis of Robust-LP.
--
--   **Formalization Note** The paper's hypothesis "(7) holds and $R^{\mathrm{out}}_{\max} < \gamma < R^{\mathrm{in}}_{\min}$", with $R^{\mathrm{in}}_{\min}$ the minimum over diagonal blocks and $R^{\mathrm{out}}_{\max}$ the maximum over off-diagonal blocks ($k \ne l$, see the printed slip in (7)), is written pairwise; the two forms are equivalent, and the pairwise form avoids a minimum or maximum over a possibly empty set. $K$, $\tau_{\mathrm{in}}$, $\tau_{\mathrm{out}}$ are arbitrary.
-- source:
--   arXiv:1912.07546v3, Lemma 1, p. 12; problem (5), p. 11; condition (7), p. 12; reference matrix (6), p. 11

import Mathlib
import Definitions.Def_RobustSpecClust_Est_Setting
open MeasureTheory ProbabilityTheory

namespace RobustSpecClust.Est

theorem lemma_1 {n m r : ℕ} (K : Matrix (Pt n m) (Pt n m) ℝ) (φ : Fin n → Fin r) (τin : ℝ)
    (τout : Fin r → Fin r → ℝ) (γ : ℝ)
    (hin : ∀ i j, φ i = φ j → γ < refMatrix K φ τin τout γ (Sum.inl i) (Sum.inl j))
    (hout : ∀ i j, φ i ≠ φ j → refMatrix K φ τin τout γ (Sum.inl i) (Sum.inl j) < γ) :
    (∀ i j, 0 ≤ trueClust (m := m) φ i j ∧ trueClust (m := m) φ i j ≤ 1) ∧
    ∀ X : Matrix (Pt n m) (Pt n m) ℝ, (∀ i j, 0 ≤ X i j ∧ X i j ≤ 1) →
      frobInner (refMatrix K φ τin τout γ - γ • ones (Pt n m)) X ≤
        frobInner (refMatrix K φ τin τout γ - γ • ones (Pt n m)) (trueClust φ) := by sorry

end RobustSpecClust.Est
