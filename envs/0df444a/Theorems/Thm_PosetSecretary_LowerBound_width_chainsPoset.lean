-- Prove2me | Theorems.Thm_PosetSecretary_LowerBound_width_chainsPoset
-- name    : PosetSecretary.LowerBound.width_chainsPoset
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T09:07:12.933479+00:00
-- url     : https://prove2.me/theorems/b1eef5c2-975f-42db-bbbf-3dc8b571c4d1
-- title:
--   Appendix F, p. 42, Figure 8 — the poset of ω disjoint k-element chains has width ω
-- statement:
--   Let $\omega\ge0$ and $k\ge1$, and let $\mathrm{Chains}(\omega,k)$ be the disjoint union of $\omega$ chains with $k$ elements each, two elements being comparable only when they lie in the same chain. Its **width**, the largest number of pairwise incomparable elements, is
--   $$\operatorname{width}\big(\mathrm{Chains}(\omega,k)\big)=\omega .$$
--
--   This is the claim that the instance of Figure 8 has width $\omega$, as Proposition 5.1 requires of its instance.
--
--   **Formalization Note** Width is the published `AppliedComb.Posets.width` (largest antichain), not a minimum number of chains. The hypothesis $k\ge1$ is necessary: for $k=0$ the poset is empty and has width $0$.
-- source:
--   Salem & Gupta, Secretary Problems with Biased Evaluations Using Partial Ordinal Information, SSRN 3444283 (version of 2022-04-17), proof of Proposition 5.1, Appendix F, p. 42, first paragraph and Figure 8

import Mathlib
import Definitions.Def_AppliedComb_Posets_width
import Definitions.Def_PosetSecretary_LowerBound_Setting

namespace PosetSecretary.LowerBound

theorem width_chainsPoset (ω k : ℕ) (hk : 1 ≤ k) :
    AppliedComb.Posets.width (ChainsPoset ω k) = ω := by sorry

end PosetSecretary.LowerBound
