-- Prove2me | Theorems.Thm_SubadditiveMMS580_Amplification_lemma_3_1
-- name    : SubadditiveMMS580.Amplification.lemma_3_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-10T19:54:21.992203+00:00
-- url     : https://prove2.me/theorems/09021cd6-5820-4d62-be55-da7957b54170
-- title:
--   Lemma 3.1 — a budgeted random bid wins half the value of a bundle with probability at least 1/2
-- statement:
--   Let $P$ be a nonempty finite set of goods, let $v:2^P\to\mathbb R$ be normalized, monotone and subadditive, and let $B>0$. A **bid vector** on $P$ is a vector $b=(b_g)_{g\in P}$ of nonnegative reals, with total $b(P)=\sum_{g\in P}b_g$; against a competing bid vector $c$, $b$ **strictly wins** the goods $\{g\in P: b_g>c_g\}$.
--
--   Then there is a finitely supported probability distribution $\sigma$ over nonnegative bid vectors on $P$ such that $b(P)\le B$ for every $b\in\operatorname{supp}(\sigma)$, and for every fixed nonnegative bid vector $c$ on $P$ with $c(P)\le B/2$,
--   $$\Pr_{b\sim\sigma}\Bigl[\,v(\{g\in P: b_g>c_g\})\ \ge\ \tfrac12\,v(P)\,\Bigr]\ \ge\ \tfrac12 .$$
--
--   The distribution is chosen once and does not depend on $c$; the budget holds in every realization, not only on average. This single-bundle bidding strategy is the building block of the independent-trials amplification in Theorem 1.4.
--
--   **Formalization Note** $P$ is `Fin s` with $s\ge1$, and bid vectors are arbitrary real vectors `Fin s → ℝ`; nonnegativity of the support and of $c$ is stated explicitly. A finitely supported distribution has a finite support with positive weights summing to one, and the probability of an event is the total weight of the support points where it holds. No positivity of $v(P)$ is assumed.
--
--   Differences from the source:
--   - encoding: a nonempty finite set $P\subseteq M$ → `Fin s` with $0<s$; reason: relabelling of a finite nonempty set; the statement involves only $P$ and $v$ on $2^P$.
--   - encoding: valuations $v:2^M\to\mathbb R_{\ge0}$ → real-valued set functions with `IsNormalized` and `IsMonotone`; reason: normalization and monotonicity give $v(S)\ge v(\varnothing)=0$, so exactly the same valuations.
--   - encoding: nonnegative bid vectors on $P$ → real vectors `Fin s → ℝ` with nonnegativity stated for every support point and for $c$; reason: the same set of vectors.
--   - encoding: finitely supported distribution $\sigma$ and $\Pr_\sigma$ → `FinDist` (finite support, positive weights summing to $1$) and `FinDist.prob` (total weight of the support points where the event holds); reason: the same objects; no measure theory needed for finite support.
-- source:
--   Bo Li, Ankang Sun, STOC 2027 submission #580 (October 2026), Lemma 3.1, p. 11

import Mathlib
import Definitions.Def_SubadditiveMMS580_Amplification_Setting
import Definitions.Def_MultiAllocToAlloc_Subadditive_Valuation
import Definitions.Def_MultiAllocToAlloc_Subadditive_Allocation
import Definitions.Def_SubmodOrder_Subadditive
import Definitions.Def_LittleCharity_MMS_Setting

open MultiAllocToAlloc.Subadditive

namespace SubadditiveMMS580.Amplification

/-- Lemma 3.1 (Li–Sun, STOC 2027 submission #580, p. 11): let `P` be a nonempty finite set (here
`Fin s`, `s ≥ 1`), `v` a normalized monotone subadditive valuation on `2^P`, and `B > 0`. There is
a finitely supported distribution `σ` over nonnegative bid vectors on `P` with `b(P) ≤ B` for every
`b` in its support such that, for every fixed nonnegative bid vector `c` with `c(P) ≤ B/2`,
`P_{b∼σ}[v({g ∈ P : b_g > c_g}) ≥ v(P)/2] ≥ 1/2`. -/
theorem lemma_3_1 (s : ℕ) (hs : 0 < s) (v : Finset (Fin s) → ℝ)
    (hnorm : IsNormalized v) (hmono : IsMonotone v) (hsub : SubmodOrder.Subadditive v)
    (B : ℝ) (hB : 0 < B) :
    ∃ σ : FinDist (Fin s → ℝ),
      (∀ b ∈ σ.support, (∀ g, 0 ≤ b g) ∧ ∑ g, b g ≤ B) ∧
      ∀ c : Fin s → ℝ, (∀ g, 0 ≤ c g) → ∑ g, c g ≤ B / 2 →
        (1 : ℝ) / 2 ≤
          σ.prob (fun b =>
            v Finset.univ / 2 ≤ v (Finset.univ.filter (fun g => c g < b g))) := by sorry

end SubadditiveMMS580.Amplification
