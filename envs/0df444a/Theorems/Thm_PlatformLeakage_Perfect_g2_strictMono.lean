-- Prove2me | Theorems.Thm_PlatformLeakage_Perfect_g2_strictMono
-- name    : PlatformLeakage.Perfect.g2_strictMono
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:41:23.947377+00:00
-- url     : https://prove2.me/theorems/3ea61645-61ad-42e8-9a8f-58bd4f66e869
-- title:
--   p. 16 / Appendix p. 2 — g2(n, v) is strictly increasing in n, so g2(N^j, v^j) ≥ g2(1, v^j)
-- statement:
--   Under the standing assumptions, for every valuation $v>0$ the function
--   $$n\longmapsto g_2(n,v)=\frac{c\mu\phi}{n}\Big(\sqrt{1+nv/(c\phi)}-1\Big)^2$$
--   is strictly increasing on $n>0$. In particular $g_2(N^j,v^j)\ge g_2(1,v^j)$ for every $N^j\ge1$.
--
--   By Lemma 2 this says that the on-platform utility rate $U^j_p(\omega,n)=\omega g_2(n,v^j)-K^j$ grows with the number of providers on the platform (the participation externality), which is why the equilibrium ranges of Proposition 1 can overlap.
--
--   **Formalization Note** The head count $n$ is a real variable here, as in the proof's derivative $\partial U^j_p/\partial n^j_p>0$.
-- source:
--   He, Savin, Goh & Teo, Off-Platform Threats in On-Demand Services, SSRN working paper 3550646 (PDF of 2021-03-25), p. 16 (PDF 16), remark after Proposition 1; proof of Proposition 1, Appendix p. 2 (PDF 37)

import Mathlib
import Definitions.Def_PlatformLeakage_Perfect_Model

namespace PlatformLeakage.Perfect

/-- p. 16 and the proof of Proposition 1 (Appendix p. 2): for a positive valuation `v`, `g2(n, v)` is
strictly increasing in the head count `n > 0`; in particular `g2(N, v) ≥ g2(1, v)` for `N ≥ 1`. -/
theorem g2_strictMono (P : Params) (hP : P.Std) (v : ℝ) (hv : 0 < v) :
    StrictMonoOn (fun n : ℝ => g2 P n v) (Set.Ioi 0) := by sorry

end PlatformLeakage.Perfect
