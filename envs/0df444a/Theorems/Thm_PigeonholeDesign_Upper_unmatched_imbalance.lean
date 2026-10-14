-- Prove2me | Theorems.Thm_PigeonholeDesign_Upper_unmatched_imbalance
-- name    : PigeonholeDesign.Upper.unmatched_imbalance
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T03:12:56.852011+00:00
-- url     : https://prove2.me/theorems/7eba3439-0db5-443e-89a7-f29539ccde67
-- title:
--   Proof of Lemma 3, p. ec8 — at most one unmatched subject per pigeonhole, H ≤ ⌈T^η⌉ and |H⁰_τ − H¹_τ| = T − τ
-- statement:
--   Fix $\eta\in(0,1)$, an even $T\ge1$, an arrival sequence $x\in[0,1]^T$, and a realization of the coins. Run the pigeonhole design with the $K=\lceil T^{\eta}\rceil$ uniform pigeonholes of $[0,1]$, and let $\tau$, the matched set $\mathcal T_M$, the unmatched set $\mathcal T_U$, and the counts $H^0_\tau$, $H^1_\tau$ be as in the proof of Lemma 3. Then:
--
--   1. every pigeonhole contains at most one unmatched subject;
--   2. in every pigeonhole, the matched subjects are split evenly between control and treatment (each pair consists of one control and one treated subject);
--   3. $H=H^0_\tau+H^1_\tau\le K=\lceil T^{\eta}\rceil$;
--   4. $$\bigl|H^0_\tau-H^1_\tau\bigr|=T-\tau .$$
--
--   The identity in item 4 says that the number of subjects forced by the balancing step equals the imbalance among the unmatched subjects; it converts the concentration of the unmatched assignments (Lemma EC.1) into a bound on $T-\tau$.
--
--   **Formalization Note** The paper's bound $H\le T^{\eta}$ becomes $H\le\lceil T^{\eta}\rceil$ because the number of pigeonholes is pinned to $\lceil T^\eta\rceil$. Item 2 is the content behind the paper's phrase "matched subjects": the pairing of the first $\tau$ subjects of each pigeonhole in arrival order (the definition of $\mathcal T_M$) produces opposite pairs. The difference in item 4 is taken in the integers.
-- source:
--   Zhao and Zhou, Pigeonhole Design: Balancing Sequential Experiments from an Online Matching Perspective, arXiv:2201.12936v6, pp. ec7-ec8 (PDF pp. 45-46), proof of Lemma 3, Component 2 (|H⁰_τ − H¹_τ| = T − τ)

import Mathlib
import Definitions.Def_PigeonholeDesign_Upper_Setting
import Definitions.Def_PigeonholeDesign_Upper_Stopping

namespace PigeonholeDesign.Upper

theorem unmatched_imbalance (η : ℝ) (hη0 : 0 < η) (hη1 : η < 1) (T : ℕ) (hT1 : 1 ≤ T)
    (hT : Even T) (x : Fin T → ℝ) (hx : ∀ t, x t ∈ Set.Icc (0 : ℝ) 1) (coin : Fin T → Bool) :
    (∀ k : ℕ, ((unmatched (uniformHole ⌈(T : ℝ) ^ η⌉₊) x coin).filter
        (fun s => uniformHole ⌈(T : ℝ) ^ η⌉₊ (x s) = k)).card ≤ 1) ∧
    (∀ k : ℕ, ((matched (uniformHole ⌈(T : ℝ) ^ η⌉₊) x coin).filter
        (fun s => uniformHole ⌈(T : ℝ) ^ η⌉₊ (x s) = k ∧
          assign (uniformHole ⌈(T : ℝ) ^ η⌉₊) x coin s = false)).card =
      ((matched (uniformHole ⌈(T : ℝ) ^ η⌉₊) x coin).filter
        (fun s => uniformHole ⌈(T : ℝ) ^ η⌉₊ (x s) = k ∧
          assign (uniformHole ⌈(T : ℝ) ^ η⌉₊) x coin s = true)).card) ∧
    H0 (uniformHole ⌈(T : ℝ) ^ η⌉₊) x coin + H1 (uniformHole ⌈(T : ℝ) ^ η⌉₊) x coin
      ≤ ⌈(T : ℝ) ^ η⌉₊ ∧
    |(H0 (uniformHole ⌈(T : ℝ) ^ η⌉₊) x coin : ℤ) - H1 (uniformHole ⌈(T : ℝ) ^ η⌉₊) x coin|
      = (T : ℤ) - tau (uniformHole ⌈(T : ℝ) ^ η⌉₊) x coin := by sorry

end PigeonholeDesign.Upper
