-- Prove2me | Theorems.Thm_ShipConsol_OneWH_lemma_E1
-- name    : ShipConsol.OneWH.lemma_E1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-18T20:13:44.471981+00:00
-- url     : https://prove2.me/theorems/066f32a4-9b83-443b-9f49-c6041aa4449c
-- title:
--   Lemma E1, p. OA1 — min(a_i + b_i) − min(a_i) ≥ b_n when b is non-increasing
-- statement:
--   Let $n \ge 1$ and let $a_1,\dots,a_n$ and $b_1,\dots,b_n$ be real numbers with $b_1 \ge b_2 \ge \dots \ge b_n$. Put $x = \min\{a_1+b_1,\dots,a_n+b_n\}$ and $y = \min\{a_1,\dots,a_n\}$. Then
--   $$x - y \ge b_n.$$
--
--   The difference of two minima is at least the smallest pairwise difference. In the paper this elementary inequality is the step that turns the unrolled form of the cost-to-go function into Lemma 2.
--
--   **Formalization Note.** The index set is `Fin (n + 1)` (so there is at least one term and the minima exist); $b_n$ is the value at the last index, and "$b_1 \ge \dots \ge b_n$" is `Antitone b`. The minima are `Finset.inf'` over all indices.
-- source:
--   Wei, Kapuscinski & Jasin, Shipping Consolidation across Two Warehouses with Delivery Deadline and Expedited Options for E-commerce and Omni-channel Retailers, author's manuscript, SSRN 2920899 (M&SOM 2020, doi:10.1287/msom.2020.0903), Online Appendix, LEMMA E1 (in the proof of Lemma 2), p. OA1

import Mathlib

namespace ShipConsol.OneWH
theorem lemma_E1 (n : ℕ) (a b : Fin (n + 1) → ℝ) (hb : Antitone b) : Finset.univ.inf' Finset.univ_nonempty (fun i => a i + b i) - Finset.univ.inf' Finset.univ_nonempty a ≥ b (Fin.last n) := by sorry
end ShipConsol.OneWH
