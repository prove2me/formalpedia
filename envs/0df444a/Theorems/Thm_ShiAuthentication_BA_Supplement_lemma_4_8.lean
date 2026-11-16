-- Prove2me | Theorems.Thm_ShiAuthentication_BA_Supplement_lemma_4_8
-- name    : ShiAuthentication.BA.Supplement.lemma_4_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T15:22:17.065707+00:00
-- url     : https://prove2.me/theorems/1db59543-2e84-4ca9-8fd1-332c357aed2a
-- title:
--   Lemma 4.8 — cut conditions for Byzantine agreement
-- statement:
--   Let $n,t$ satisfy the standing assumption $2t<n\le 3t$ of §4.3 and put $r=n-2t$. Let $G$ be an authentication graph on the $n$ parties, and fix a knowledge setting (public authentication graph, or local key tables only).
--
--   1. If Byzantine agreement with fault bound $t$ is possible on $G$, then $G$ has an edge from every $r$-set to every disjoint $r$-set: for all disjoint $X,Y\subseteq P$ with $|X|=|Y|=r$ there are $x\in X$, $y\in Y$ with $x\to y$.
--   2. Conversely, if $G$ has an edge from every $\lceil r/2\rceil$-set to every disjoint $r$-set, then Byzantine agreement with fault bound $t$ is possible on $G$.
--
--   $$\text{BA feasible on } G\ \Longrightarrow\ \mathrm{Cut}_G(r,r),\qquad \mathrm{Cut}_G(\lceil r/2\rceil,r)\ \Longrightarrow\ \text{BA feasible on } G.$$
--
--   The two cut conditions sandwich the feasible graphs between two purely combinatorial classes; they reduce the authentication complexity of agreement to extremal edge counting (Lemmas 4.9 and 4.10, Theorem 4.11).
--
--   Differences from the source:
--   - encoding: ⌈r/2⌉ → (r + 1) / 2 in ℕ; reason: equal for every natural r
--   - reading: feasible BA graph (setting not named in the lemma) → BAPossible mode t G for each knowledge setting mode; reason: §3.1 and Theorem 4.1 state that the characterization, hence feasibility, is the same in both settings; the stronger reading claims the lemma in each
-- source:
--   Kecheng Shi, STOC 2027 submission #203 (October 2026), Lemma 4.8, p. 22 (standing assumptions of §4.3, p. 22)

import Definitions.Def_ShiAuthentication_BA_Supplement_Complexity

set_option autoImplicit false

namespace ShiAuthentication.BA.Supplement

/-- **Lemma 4.8 (Cut conditions)**, p. 22, under the standing assumptions of §4.3:
`2t < n ≤ 3t` and `r = n − 2t`. In either knowledge setting, every graph on which Byzantine
agreement is possible has an edge from every `r`-set to every disjoint `r`-set; conversely, an
edge from every `⌈r/2⌉`-set to every disjoint `r`-set suffices for Byzantine agreement.
`⌈r/2⌉` is written `(r + 1) / 2` (natural-number division). -/
theorem lemma_4_8 (n t r : ℕ) (h2t : 2 * t < n) (h3t : n ≤ 3 * t) (hr : r = n - 2 * t)
    (mode : Knowledge) (G : AuthGraph n) :
    (BAPossible mode t G → CutCondition G r r) ∧
    (CutCondition G ((r + 1) / 2) r → BAPossible mode t G) := by sorry

end ShiAuthentication.BA.Supplement
