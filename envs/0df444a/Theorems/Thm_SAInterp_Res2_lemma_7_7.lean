-- Prove2me | Theorems.Thm_SAInterp_Res2_lemma_7_7
-- name    : SAInterp.Res2.lemma_7_7
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T22:41:57.315205+00:00
-- url     : https://prove2.me/theorems/0c750220-0e7d-4d8d-81c5-b66b5f4f5411
-- title:
--   Lemma 7.7 — E_{D_k}[C | π] = h·P_{π,C}(k) with P an alternating sum of Q's; Σ δ_i ≤ bdeg(C)/n without bottom-row selectors
-- statement:
--   For all sufficiently large $n$, with $d=\lfloor n/100\rfloor$, the following holds. Let $\pi$ be any layer permutations and let $C$ be an indicator conjunction of $\mathrm{CPLS}_n$ with $\mathrm{bdeg}(C)\le d$. Then there exist
--   - a set $B\subseteq[n]\setminus\{1\}$,
--   - an integer $a\ge0$ with $a+|B|\le\mathrm{bdeg}(C)$,
--   - numbers $\delta_i\ge0$ for $i\in B$,
--   - a number $h=h_{\pi,C}(n)\ge0$ that does not depend on $k$,
--
--   such that the polynomial
--   $$P_{\pi,C}(z)=\sum_{T\subseteq B}(-1)^{|T|}Q_{a+|T|}(z)\prod_{j\in T}\delta_j$$
--   has degree at most $\mathrm{bdeg}(C)$ and satisfies $h\,P_{\pi,C}(k)=E_{D_k}[C\mid\pi]$ for every $k\in[n]$. Moreover, if $C$ contains no selector indicator $[\![e_u=\sigma]\!]$ with $u$ on row $n$, then $\sum_{i\in B}\delta_i\le\mathrm{bdeg}(C)/n$.
--
--   The lemma gives the syntactic form of the polynomial interpolated by $E_\mu$, which the positivity proof (Lemma 7.2) needs.
--
--   Differences from the source:
--   - reading: the standing assumption of §6 "Let n be sufficiently large" → ∃ N0, ∀ n ≥ N0; reason: explicit form of the standing assumption.
--   - reading: d = n/100 → d = ⌊n/100⌋; reason: µ needs an integer d, and the proofs use only d ≤ n/100.
--   - encoding: the non-negative function h_{π,C}(n) → a real h ≥ 0 chosen for each n, π, C, quantified before k; "the degree ≤ bdeg(C) polynomial" → a clause natDegree ≤ bdeg C; δ → a function on Fin n of which only the values on B matter; reason: Lean convention, same statement.
--   - encoding: 0-based indices (row n is row n − 1, [n] ∖ {1} is {i : i ≠ 0}); reason: Lean indexing.
-- source:
--   Acheampong, Davis, Robere, Polynomial Interpolation for Sherali-Adams Lower Bounds, STOC 2027 submission (manuscript sha256 8de0a787…), p. 35 (PDF p. 37), Lemma 7.7

import Mathlib
import Definitions.Def_SAInterp_Res2_Indicator
import Definitions.Def_SAInterp_Res2_CPLS
import Definitions.Def_SAInterp_Res2_CPLSDist

open Polynomial

namespace SAInterp.Res2

/-- Lemma 7.7 (p. 35), for all sufficiently large `n` (standing assumption of §6), with
`d = ⌊n/100⌋`: for any layer permutations `π` and any indicator conjunction `C` with
`bdeg(C) ≤ d` there are `B ⊆ [n] ∖ {1}`, `a ∈ ℕ` with `a + |B| ≤ bdeg(C)`, `δ_i ≥ 0` (`i ∈ B`)
and `h ≥ 0` such that `P(z) = ∑_{T ⊆ B} (−1)^{|T|} Q_{a+|T|}(z) ∏_{j ∈ T} δ_j` has degree
`≤ bdeg(C)` and `h · P(k) = E_{D_k}[C | π]` for every `k ∈ [n]`; moreover, if `C` has no
selector indicator `⟦e_u = σ⟧` with `u` on the bottom row, then `∑_{i ∈ B} δ_i ≤ bdeg(C)/n`. -/
theorem lemma_7_7 :
    ∃ N0 : ℕ, ∀ n : ℕ, N0 ≤ n → ∀ (π : LayerPerms n) (C : IndConj (cplsSize n)),
      bdeg C ≤ cplsD n →
      ∃ (B : Finset (Fin n)) (a : ℕ) (δ : Fin n → ℝ) (h : ℝ),
        (∀ i ∈ B, i.val ≠ 0) ∧ a + B.card ≤ bdeg C ∧ (∀ i ∈ B, 0 ≤ δ i) ∧ 0 ≤ h ∧
        (lemma77Poly n a B δ).natDegree ≤ bdeg C ∧
        (∀ k : ℕ, 1 ≤ k → k ≤ n →
          h * (lemma77Poly n a B δ).eval (k : ℝ) = EDkAlgCond n k π (indConj C)) ∧
        ((∀ x ∈ C, ∀ i j : Fin n, x.1 = CPLSVar.sel i j → i.val + 1 ≠ n) →
          ∑ i ∈ B, δ i ≤ (bdeg C : ℝ) / n) := by sorry

end SAInterp.Res2
