-- Prove2me | Theorems.Thm_RandKSATSample_Main_lemma_4_8
-- name    : RandKSATSample.Main.lemma_4_8
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T03:01:14.213197+00:00
-- url     : https://prove2.me/theorems/3f7fff5e-006c-4f15-8009-39bb38b9e1ba
-- title:
--   Lemma 4.8 — exploration bound: for every finite truncation Λ ⊆ {Γ : |J_Γ| ≥ 2}, max_j E_ζ[2^{|A_j|} e^{R(A_j)}] ≤ 2n^{γ_mix}
-- statement:
--   Under the assumptions of §4 ($n\ge2$, $k\ge30$, (4.1), (4.5)–(4.8)), fix an arbitrary finite set $\Lambda$ of cluster labels with $|J_\Gamma|\ge2$ for every $\Gamma\in\Lambda$. Let $\zeta$ be the random labelled hypergraph on the blocks $[s]$ that keeps each candidate $\Gamma\in\Lambda$, with vertex set $J_\Gamma$, independently with probability $1-e^{-2|a_\Gamma|}$; let $A_j$ be the vertex set of the component of $\zeta$ containing $j$ and $R(A)=\sum_{\Gamma\in\Lambda:J_\Gamma\cap A\neq\emptyset}|a_\Gamma|$. Then
--   $$\max_j\mathbb E_\zeta\big[2^{|A_j|}e^{R(A_j)}\big]\le2n^{\gamma_{\mathrm{mix}}},\qquad\gamma_{\mathrm{mix}}=\frac{64\rho e^{-2\tau}}{1-25/(3k^3)},$$
--   uniformly in $j$ and in $\Lambda$. With Lemma 4.4 it gives the variance constant of Theorem 4.1.
--
--   Differences from the source:
--   - reading: the standing assumptions of §4.3 (n ≥ 2, k ≥ 30, (4.1), (4.5)–(4.8), parameters (4.4)) → hypotheses hn, hk, Cond41, Cond45, Cond46, Cond47, Cond48; reason: Lemma 4.8 is printed without hypotheses inside §4, whose assumptions are those of Theorem 4.1 (p. 22); the proof uses (4.6), (4.67) (k ≥ 30) and Lemmas 4.10–4.13
--   - encoding: max_j E_ζ[…] ≤ 2n^{γ_mix} → ∀ j : Blk Φ, hyperMoment … j ≤ 2 n^{γ_mix}; reason: a maximum over the blocks is bounded iff every term is
-- source:
--   He, Li, Yang, Fast Almost-Uniform Sampling of Random k-SAT Solutions, arXiv:2610.10474 (version not printed; file sha256 563a4d84…), p. 32, Lemma 4.8

import Mathlib
import Definitions.Def_RandKSATSample_Main_Formula
import Definitions.Def_RandKSATSample_Main_Structure
import Definitions.Def_RandKSATSample_Main_PolymerModel
import Definitions.Def_RandKSATSample_Main_FiniteInteraction
import Definitions.Def_RandKSATSample_Main_CoreChain

set_option autoImplicit false

namespace RandKSATSample.Main

/-- Lemma 4.8: under the assumptions of §4 (those of Theorem 4.1), for every finite set `Λ` of
cluster labels with `|J_Γ| ≥ 2`, the random hypergraph on the blocks with hyperedges `J_Γ`,
`Γ ∈ Λ`, retained independently with probability `1 − e^{−2|a_Γ|}`, satisfies
`max_j E_ζ[2^{|A_j|} e^{R(A_j)}] ≤ 2 n^{γ_mix}`. -/
theorem lemma_4_8 {n m k : ℕ} (Φ : Formula n m k) (hn : 2 ≤ n) (hk : 30 ≤ k)
    (h41 : Cond41 Φ) (h45 : Cond45 Φ) (h46 : Cond46 Φ) (h47 : Cond47 Φ) (h48 : Cond48 Φ)
    (Λ : Finset (ClusterLabel (Poly Φ))) (hΛ : ∀ Γ ∈ Λ, 2 ≤ (JGam Φ Γ).card) (j : Blk Φ) :
    hyperMoment (fun Γ : {Γ // Γ ∈ Λ} => JGam Φ Γ.1) (fun Γ => aGam Φ Γ.1) j ≤
      2 * (n : ℝ) ^ gammaMix n m k := by sorry

end RandKSATSample.Main
