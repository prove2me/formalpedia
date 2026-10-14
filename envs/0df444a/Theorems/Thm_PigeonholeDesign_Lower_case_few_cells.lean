-- Prove2me | Theorems.Thm_PigeonholeDesign_Lower_case_few_cells
-- name    : PigeonholeDesign.Lower.case_few_cells
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T05:19:17.60499+00:00
-- url     : https://prove2.me/theorems/aeebb9eb-d167-4951-b251-fd0ce92f9f57
-- title:
--   Proof of Lemma 4, p. ec15 — with at most K ≤ C₀T^{1/2} interval pigeonholes some instance forces expected discrepancy ≥ c T^{1/4}
-- statement:
--   Consider the pigeonhole design on $[0,1]$ whose pigeonholes are the intervals $[l_0,l_1),\dots,[l_{K-2},l_{K-1}),[l_{K-1},l_K]$ of breakpoints $0=l_0<l_1<\dots<l_K=1$. For every constant $C_0>0$ there are a constant $c>0$ and a threshold $T_0$, depending only on $C_0$, such that for every even $T\ge T_0$ and every such partition with
--   $$K\le C_0\,T^{1/2}$$
--   pigeonholes, some arrival sequence $x\in[0,1]^T$ gives
--   $$\mathbb E\bigl[d_{A,B}\bigr]\;\ge\;c\,T^{1/4},$$
--   the expectation being over the fair coins of the design.
--
--   This is the first of the two cases into which the proof of Lemma 4 splits: when there are few pigeonholes, the alternating instance with counts proportional to $L_k^2$ yields a discrepancy of order $\sqrt{T/K}\ge T^{1/4}$.
--
--   **Formalization Note** "$K=O(T^{1/2})$" is read as $K\le C_0\sqrt T$ for an arbitrary fixed constant $C_0>0$. The constants $c$ and $T_0$ depend on $C_0$ only: they are chosen before $T$, $K$ and the breakpoints, and the hard instance is chosen after the partition. The paper's counts $n_k=L_k^2T/\sum_i L_i^2$ are not even integers in general; the statement asserts only that a hard instance exists, so the rounding is left to the proof.
-- source:
--   Zhao and Zhou, Pigeonhole Design: Balancing Sequential Experiments from an Online Matching Perspective, arXiv:2201.12936v6, p. ec15, proof of Lemma 4 (case K = O(T^{1/2}))

import Mathlib
import Definitions.Def_PigeonholeDesign_Lower_Setting

namespace PigeonholeDesign.Lower

theorem case_few_cells :
    ∀ C₀ : ℝ, 0 < C₀ → ∃ c : ℝ, 0 < c ∧ ∃ T₀ : ℕ, ∀ T : ℕ, T₀ ≤ T → Even T →
      ∀ (K : ℕ) (_hK : 1 ≤ K) (b : Breakpoints K), (K : ℝ) ≤ C₀ * Real.sqrt T →
        ∃ x : Fin T → ℝ, (∀ t, x t ∈ Set.Icc (0 : ℝ) 1) ∧
          c * (T : ℝ) ^ ((1 : ℝ) / 4) ≤ PigeonholeDesign.Upper.phdExp (intervalHole b) x := by sorry

end PigeonholeDesign.Lower
