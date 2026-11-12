-- Prove2me | Theorems.Thm_RelatedSchedFPTAS796_Main_lemma_5_6
-- name    : RelatedSchedFPTAS796.Main.lemma_5_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T07:12:27.985216+00:00
-- url     : https://prove2.me/theorems/7a537bae-3dac-46f7-bbbe-bfb1c1709ad9
-- title:
--   Lemma 5.6 — extracting a repeated sumset $k'B\subseteq A_1+\dots+A_k$ with $k'|B|\ge\sum|A_i|/(2(1+\lfloor\log k\rfloor))$
-- statement:
--   Let $\varepsilon>0$ and let $A_1,\dots,A_k\subseteq[0,2/\varepsilon]^d\cap\mathbb Z^d$, $k\ge1$, be axis-projection closed sets containing zero. There are an integer $1\le k'\le k$ and an axis-projection closed set $B\subseteq[0,2/\varepsilon]^d\cap\mathbb Z^d$ containing zero such that
--   $$k'B\subseteq A_1+\dots+A_k,\qquad k'|B|\ \ge\ \frac{\sum_{i=1}^k|A_i|}{2(1+\lfloor\log k\rfloor)}.$$
--   If in addition $\sum_i|A_i|>2k(1+\lfloor\log k\rfloor)(2/\varepsilon+1)^{d-1}$, then $B$ contains a positive multiple of every coordinate vector $e_j$. Logarithms are base 2.
--
--   The lemma turns a large sum of profile sets into a repeated sumset $k'B$ whose generating set spans a full-dimensional lattice, so that Theorem 1.3 applies (Lemma 5.7).
--
--   **Formalization Note** $\lfloor\log k\rfloor$ is `Nat.log 2 k`; $d-1$ is natural subtraction (for $d=0$ the additional hypothesis cannot hold, since every $A_i=\{0\}$).
--
--   Differences from the source:
--   - generalization: $1/\varepsilon$ a power of two (§2.1 convention) → any real $\varepsilon>0$; reason: the statement and proof use $2/\varepsilon$ only as a bound; the power-of-two case is a special case
-- source:
--   Lin Chen, Tingwei Hu, Jiayi Lian, Yuchen Mao, Guochuan Zhang, Faster Approximation Schemes for Scheduling on Related Machines, STOC 2027 submission #796 (October 2026), source.pdf SHA-256 5d7d0135eed9cbe942c80598e2bb07d8c56ab67aec0d6e8486a067237654f7f3, p.15, Lemma 5.6 (proof p.15)

import Mathlib
import Definitions.Def_RelatedSchedFPTAS796_Main_Model

set_option autoImplicit false

open Pointwise

namespace RelatedSchedFPTAS796.Main

/-- **Lemma 5.6**, p.15 (proof p.15). Let `A_1, …, A_k ⊆ [0, 2/ε]^d ∩ ℤ^d` be axis-projection
closed sets containing zero. There are an integer `1 ≤ k' ≤ k` and an axis-projection closed set
`B ⊆ [0, 2/ε]^d ∩ ℤ^d` containing zero with `k'B ⊆ A_1 + ⋯ + A_k` and
`k'|B| ≥ (∑_i |A_i|)/(2(1 + ⌊log k⌋))`. If in addition
`∑_i |A_i| > 2k(1 + ⌊log k⌋)(2/ε + 1)^{d−1}`, then `B` contains a positive multiple of every
coordinate vector. (`log` is base 2; `k ≥ 1`; any real `ε > 0`.) -/
theorem lemma_5_6 {d k : ℕ} (ε : ℝ) (hε : 0 < ε) (hk : 1 ≤ k) (A : Fin k → Finset (Fin d → ℤ))
    (hbox : ∀ i, ∀ x ∈ A i, ∀ j, 0 ≤ x j ∧ (x j : ℝ) ≤ 2 / ε)
    (hcl : ∀ i, AxisProjClosed (A i : Set (Fin d → ℤ))) (h0 : ∀ i, (0 : Fin d → ℤ) ∈ A i) :
    ∃ k' : ℕ, 1 ≤ k' ∧ k' ≤ k ∧ ∃ B : Finset (Fin d → ℤ),
      (∀ x ∈ B, ∀ j, 0 ≤ x j ∧ (x j : ℝ) ≤ 2 / ε) ∧ AxisProjClosed (B : Set (Fin d → ℤ)) ∧
      (0 : Fin d → ℤ) ∈ B ∧
      k' • (B : Set (Fin d → ℤ)) ⊆ ∑ i, (A i : Set (Fin d → ℤ)) ∧
      (∑ i, ((A i).card : ℝ)) / (2 * (1 + (Nat.log 2 k : ℝ))) ≤ k' * B.card ∧
      ((2 * k * (1 + (Nat.log 2 k : ℝ)) * (2 / ε + 1) ^ (d - 1) < ∑ i, ((A i).card : ℝ)) →
        ∀ j : Fin d, ∃ c : ℤ, 0 < c ∧ Pi.single j c ∈ B) := by sorry

end RelatedSchedFPTAS796.Main
