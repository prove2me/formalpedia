-- Prove2me | Theorems.Thm_PigeonholeDesign_Lower_jensen_display
-- name    : PigeonholeDesign.Lower.jensen_display
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T05:19:19.783766+00:00
-- url     : https://prove2.me/theorems/a8163e80-951a-46b8-a087-c41c181ab9fa
-- title:
--   Proof of Lemma 4, p. ec15 — if Σ L_k = 1 then √(T Σ L_k²) ≥ √T √(K(1/K)²) = √(T/K), with equality iff L_k = 1/K
-- statement:
--   Let $K\ge1$, let $L_1,\dots,L_K$ be real numbers with $\sum_k L_k=1$, and let $T$ be a natural number. Then
--   $$\sqrt{T\sum_{k=1}^K L_k^2}\;\ge\;\sqrt T\,\sqrt{K\Bigl(\frac1K\Bigr)^2}\;=\;\sqrt{\frac TK},$$
--   and, when $T>0$, the inequality is an equality if and only if $L_k=1/K$ for every $k$.
--
--   The inequality is Jensen's inequality for the convex function $L\mapsto L^2$. In the proof of Lemma 4 it bounds the cell-length factor $\sqrt{T\sum_k L_k^2}$ of a partition of $[0,1]$ into $K$ intervals from below by $\sqrt{T/K}$, uniformly over the partition.
--
--   **Formalization Note** In the paper the $L_k$ are the cell lengths; the statement holds for any reals summing to $1$. The equality clause needs $T>0$ (at $T=0$ both sides vanish).
-- source:
--   Zhao and Zhou, Pigeonhole Design: Balancing Sequential Experiments from an Online Matching Perspective, arXiv:2201.12936v6, p. ec15, proof of Lemma 4 (Jensen display)

import Mathlib
import Definitions.Def_PigeonholeDesign_Lower_Setting

namespace PigeonholeDesign.Lower

theorem jensen_display {K : ℕ} (hK : 1 ≤ K) (L : Fin K → ℝ) (hsum : ∑ k, L k = 1) (T : ℕ) :
    Real.sqrt T * Real.sqrt (K * (1 / (K : ℝ)) ^ 2) ≤ Real.sqrt (T * ∑ k, L k ^ 2) ∧
      Real.sqrt T * Real.sqrt (K * (1 / (K : ℝ)) ^ 2) = Real.sqrt (T / K) ∧
      (0 < T → (Real.sqrt (T * ∑ k, L k ^ 2) = Real.sqrt (T / K) ↔ ∀ k, L k = 1 / K)) := by sorry

end PigeonholeDesign.Lower
