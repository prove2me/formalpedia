-- Prove2me | Theorems.Thm_PrivOptTest_search_bad_event
-- name    : PrivOptTest.search_bad_event
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T17:00:12.218395+00:00
-- url     : https://prove2.me/theorems/24f439b3-8abf-4ba5-a392-716c48ac5b0c
-- title:
--   Proof of Theorem 3.12, Step 1, (8)–(9), pp.21–22 — the private binary search
-- statement:
--   Run Algorithm 2 on blocks $A,B$ of $k\ge1$ records in $\{0,1\}^b$, $b\ge2$, with $\varepsilon>0$, $\beta\in(0,1]$. The bad event $\mathcal B_{bs}=\{\exists t\le T:|F(\ell_t)-\hat F(\ell_t)|\ge\alpha/20\}$, the $\ell_t$ being the adaptively chosen depths, has
--   $$\Pr(\mathcal B_{bs})\le T\beta_0 .$$
--   If moreover the promise holds and $k\ge4\alpha$, then off $\mathcal B_{bs}$ the search ends with $H=L+1$ and
--   $$F(L)\le\hat F(L)+\frac\alpha{20}\le\frac{21\alpha}{20},\qquad F(H)\ge\hat F(H)-\frac\alpha{20}\ge\frac{19\alpha}{20}.\qquad(9)$$
--
--   These are the two facts about the search that both cases of the analysis use.
--
--   Differences from the source:
--   - reading: n in Algorithm 2 → the block size k; reason: Remark 3.6 and "Fix k = ⌊t/2⌋" (p.16): the algorithm runs on the blocks
--   - reading: (9) "under the event B^c_bs" → under B^c_bs, the promise and k ≥ 4α; reason: the endpoints L = 0, H = b keep the exact values F̂(0) = 0 = F(0) and F̂(b) = k, which equals F(b) only under the promise (Lemma 3.10) and is ≥ α only for k ≥ α; both are standing assumptions of the proof (p.22)
--   - generalization: ε ∈ (0,1], β ∈ (0,1/3], b = ⌈log₂ m⌉ + 1 → ε > 0, β ∈ (0,1], b ≥ 2, k ≥ 1; reason: the argument uses only these; specializes to the source
--   - encoding: Pr(B_bs) ≤ T·β₀ ≤ β → Pr(B_bs) ≤ T·β₀; reason: the first inequality of the chain; T·β₀ = β/2
-- source:
--   M. Haghifam, K. K. Patel, A. Blum, G. Fanti, J. Ziani, Should We Combine Our Data? Algorithms and Limits for Privately Assessing Data Sharing, arXiv:2611.03599 (manuscript sha256 4ac94dcf…), proof of Theorem 3.12, Step 1, (8), p.21 and (9), p.22

import Mathlib
import Definitions.Def_PrivOptTest_searchRun

open MeasureTheory

namespace PrivOptTest

/-- **Proof of Theorem 3.12, Step 1, (8)–(9)** (pp.21–22). For every pair of blocks of size `k` (no
promise needed), the bad event `B_bs = {∃ t ≤ T : |F(ℓ_t) − F̂(ℓ_t)| ≥ α/20}` of the private binary
search has probability at most `T·β₀`, the `ℓ_t` being the adaptively chosen depths. On its complement,
under the promise and `n ≥ 4α`, the search ends with `H = L + 1` and
`F(L) ≤ F̂(L) + α/20 ≤ 21α/20`, `F(H) ≥ F̂(H) − α/20 ≥ 19α/20`.
Source: Haghifam, Patel, Blum, Fanti, Ziani, *Should We Combine Our Data?*, arXiv:2611.03599 (manuscript sha256 4ac94dcf…), proof of Theorem 3.12, Step 1, (8) p.21 and (9) p.22.

**Formalization Note.** `n` is the block size `k`, `F` is `escaped`, and the search state after `T`
passes is the final one. `T·β₀ = β/2`. Records are integers below `2^b`. -/
theorem search_bad_event (b k : ℕ) (ε β : ℝ) (hb : 2 ≤ b) (hk : 1 ≤ k) (hε : 0 < ε) (hβ0 : 0 < β)
    (hβ1 : β ≤ 1) (A B : List ℕ) (hAl : A.length = k) (hBl : B.length = k)
    (hA : ∀ x ∈ A, x < 2 ^ b) (hB : ∀ x ∈ B, x < 2 ^ b) :
    (algo2 b k ε β).coinLaw (searchBad b k ε β A B) ≤
        ENNReal.ofReal ((realParams b k ε β).T * (realParams b k ε β).β₀) ∧
      (Promise A B → 4 * (realParams b k ε β).α ≤ k → ∀ ω ∉ searchBad b k ε β A B,
        (searchRun b k ε β A B ω (realParams b k ε β).T).H =
            (searchRun b k ε β A B ω (realParams b k ε β).T).L + 1 ∧
          (escaped k b (searchRun b k ε β A B ω (realParams b k ε β).T).L A B : ℝ) ≤
            (searchRun b k ε β A B ω (realParams b k ε β).T).FL + (realParams b k ε β).α / 20 ∧
          (searchRun b k ε β A B ω (realParams b k ε β).T).FL + (realParams b k ε β).α / 20 ≤
            21 * (realParams b k ε β).α / 20 ∧
          (searchRun b k ε β A B ω (realParams b k ε β).T).FH - (realParams b k ε β).α / 20 ≤
            (escaped k b (searchRun b k ε β A B ω (realParams b k ε β).T).H A B : ℝ) ∧
          19 * (realParams b k ε β).α / 20 ≤
            (searchRun b k ε β A B ω (realParams b k ε β).T).FH - (realParams b k ε β).α / 20) := by sorry

end PrivOptTest
