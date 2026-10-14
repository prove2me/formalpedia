-- Prove2me | Theorems.Thm_PigeonholeDesign_Lower_case_many_cells
-- name    : PigeonholeDesign.Lower.case_many_cells
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T05:19:35.236553+00:00
-- url     : https://prove2.me/theorems/693ae1bd-8e0a-4c67-ade5-8fa45302edd9
-- title:
--   Proof of Lemma 4, pp. ec15–ec16 — with at least K ≥ C₀T^{1/2} interval pigeonholes some instance forces expected discrepancy ≥ c T^{1/4}
-- statement:
--   Consider the pigeonhole design on $[0,1]$ whose pigeonholes are the intervals $[l_0,l_1),\dots,[l_{K-2},l_{K-1}),[l_{K-1},l_K]$ of breakpoints $0=l_0<l_1<\dots<l_K=1$. For every constant $C_0>0$ there are a constant $c>0$ and a threshold $T_0$, depending only on $C_0$, such that for every even $T\ge T_0$ and every such partition with
--   $$K\ge C_0\,T^{1/2}$$
--   pigeonholes, some arrival sequence $x\in[0,1]^T$ gives
--   $$\mathbb E\bigl[d_{A,B}\bigr]\;\ge\;c\,T^{1/4},$$
--   the expectation being over the fair coins of the design.
--
--   This is the second case of the proof of Lemma 4: with many pigeonholes, an instance with an odd number of subjects in each pigeonhole leaves one unmatched subject per pigeonhole, and matching these unmatched subjects across pigeonholes costs of order $K^{1/2}\ge T^{1/4}$ in expectation.
--
--   **Formalization Note** "$|\mathcal S|=\Omega(T^{1/2})$" is read as $K\ge C_0\sqrt T$ for an arbitrary fixed constant $C_0>0$. The constants $c$ and $T_0$ depend on $C_0$ only and are chosen before $T$, $K$ and the breakpoints; the hard instance is chosen after the partition. The paper sketches this case in two sentences and does not specify the instance; the statement asserts only that a hard instance exists.
-- source:
--   Zhao and Zhou, Pigeonhole Design: Balancing Sequential Experiments from an Online Matching Perspective, arXiv:2201.12936v6, pp. ec15-ec16, proof of Lemma 4 (case |S| = Omega(T^{1/2}))

import Mathlib
import Definitions.Def_PigeonholeDesign_Lower_Setting

namespace PigeonholeDesign.Lower

theorem case_many_cells :
    ∀ C₀ : ℝ, 0 < C₀ → ∃ c : ℝ, 0 < c ∧ ∃ T₀ : ℕ, ∀ T : ℕ, T₀ ≤ T → Even T →
      ∀ (K : ℕ) (_hK : 1 ≤ K) (b : Breakpoints K), C₀ * Real.sqrt T ≤ (K : ℝ) →
        ∃ x : Fin T → ℝ, (∀ t, x t ∈ Set.Icc (0 : ℝ) 1) ∧
          c * (T : ℝ) ^ ((1 : ℝ) / 4) ≤ PigeonholeDesign.Upper.phdExp (intervalHole b) x := by sorry

end PigeonholeDesign.Lower
