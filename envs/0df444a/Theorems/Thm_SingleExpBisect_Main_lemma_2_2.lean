-- Prove2me | Theorems.Thm_SingleExpBisect_Main_lemma_2_2
-- name    : SingleExpBisect.Main.lemma_2_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T17:39:42.808756+00:00
-- url     : https://prove2.me/theorems/db406829-130c-480f-a466-d7dff68b4646
-- title:
--   Lemma 2.2 — truncated exp–log identity ⟨exp(⟨log Z⟩)⟩ = ⟨Z⟩
-- statement:
--   Let $Z\in\mathbb Q[[X]]$ have constant term one (so $\log Z$ is defined), and let $U$ be a set of monomials closed under multiplication by monomials. Writing $\langle F\rangle$ for $F$ with the monomials of $U$ discarded,
--   $$\big\langle\exp\big(\langle\log Z\rangle\big)\big\rangle=\langle Z\rangle .$$
--   The paper's case is $U=\{m:\deg m>D\}$, i.e. $\langle\exp(\langle\log Z\rangle_{\deg\le D})\rangle_{\deg\le D}=\langle Z\rangle_{\deg\le D}$.
--
--   Differences from the source:
--   - generalization: the truncation ⟨·⟩_{deg ≤ D} → the truncation discarding any upward-closed set U of monomials; reason: U = {deg > D} gives the printed statement; §3 applies the lemma to the multi-degree truncation ≤(k,n,2k) (p. 22), and the printed proof covers every such U
--   - generalization: a finite variable set X → any variable type σ; reason: the printed case is σ finite
--   - encoding: "the formal logarithm of Z is defined" → constantCoeff Z = 1; reason: (2) defines log F for constant term one
--   - encoding: log and exp as the series (2), (3) → logPS, expPS defined coefficientwise by finite sums; reason: equal to (2) and (3) under the constant-term conditions; exp is applied to ⟨log Z⟩, whose constant term is 0
-- source:
--   Kumabe, Single-Exponential FPT Algorithms for Minimum Bisection and Matching Cut via a New Unbreakable Decomposition, arXiv:2611.05982 (October 2026 version; PDF SHA256 6530ce94…6b76541), §2, p. 14, Lemma 2.2

import Mathlib
import Definitions.Def_SingleExpBisect_Main_FormalSeries

open scoped Classical

namespace SingleExpBisect.Main

/-- Kumabe, *Single-Exponential FPT Algorithms for Minimum Bisection and Matching Cut via a New
Unbreakable Decomposition*, arXiv:2611.05982 (October 2026), §2, p. 14, Lemma 2.2: if the formal
logarithm of `Z` is defined (constant term one), then
`⟨exp(⟨log Z⟩)⟩ = ⟨Z⟩`, for every truncation `⟨·⟩` that discards a set `U` of monomials closed
under multiplication by monomials; `⟨·⟩_{deg ≤ D}` is the case `U = {m : deg m > D}`. -/
theorem lemma_2_2 {σ : Type} (U : Set (σ →₀ ℕ)) (hU : IsUpClosed U) (Z : MvPowerSeries σ ℚ)
    (hZ : MvPowerSeries.constantCoeff Z = 1) :
    discard U (expPS (discard U (logPS Z))) = discard U Z := by sorry

end SingleExpBisect.Main
