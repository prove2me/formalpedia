-- Prove2me | Theorems.Thm_PigeonholeDesign_Lower_cauchy_schwarz_display
-- name    : PigeonholeDesign.Lower.cauchy_schwarz_display
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T05:19:10.351393+00:00
-- url     : https://prove2.me/theorems/288a4147-d462-4423-8a37-2c55d60835ca
-- title:
--   Proof of Lemma 4, p. ec15 — with n_k = L_k² T/Σ L_i², Σ L_k √n_k = √((Σ L_k²)(Σ n_k)) = √(T Σ L_k²)
-- statement:
--   Let $L_1,\dots,L_K\ge0$ be real numbers with $\sum_i L_i^2>0$, let $T$ be a natural number, and put
--   $$n_k=\frac{L_k^2}{\sum_{i=1}^K L_i^2}\,T\qquad(k=1,\dots,K).$$
--   Then
--   $$\sum_{k=1}^K L_k\,(n_k)^{1/2}=\sqrt{\Bigl(\sum_{k=1}^K L_k^2\Bigr)\Bigl(\sum_{k=1}^K n_k\Bigr)}=\sqrt{T\sum_{k=1}^K L_k^2}.$$
--
--   The first equality is the equality case of the Cauchy–Schwarz inequality, since $\sqrt{n_k}$ is proportional to $L_k$; the second holds because $\sum_k n_k=T$. In the proof of Lemma 4 this turns the per-pigeonhole bound $c\sum_k L_k\sqrt{n_k}$ into $c\sqrt{T\sum_k L_k^2}$.
--
--   **Formalization Note** In the paper the $L_k$ are the lengths of the cells of a partition of $[0,1]$; the identity is stated for any nonnegative reals with positive sum of squares, which covers them. The $n_k$ are real numbers here, as in the display.
-- source:
--   Zhao and Zhou, Pigeonhole Design: Balancing Sequential Experiments from an Online Matching Perspective, arXiv:2201.12936v6, p. ec15, proof of Lemma 4 (Cauchy-Schwarz display)

import Mathlib
import Definitions.Def_PigeonholeDesign_Lower_Setting

namespace PigeonholeDesign.Lower

theorem cauchy_schwarz_display {K : ℕ} (L : Fin K → ℝ) (T : ℕ) (hL : ∀ k, 0 ≤ L k)
    (hS : 0 < ∑ i, L i ^ 2) :
    ∑ k, L k * Real.sqrt (L k ^ 2 / (∑ i, L i ^ 2) * T) =
        Real.sqrt ((∑ k, L k ^ 2) * ∑ k, L k ^ 2 / (∑ i, L i ^ 2) * T) ∧
      Real.sqrt ((∑ k, L k ^ 2) * ∑ k, L k ^ 2 / (∑ i, L i ^ 2) * T) =
        Real.sqrt (T * ∑ k, L k ^ 2) := by sorry

end PigeonholeDesign.Lower
