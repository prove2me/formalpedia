-- Prove2me | Theorems.Thm_SetCoverThreshold_MaxCover_max_k_cover_threshold
-- name    : SetCoverThreshold.MaxCover.max_k_cover_threshold
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T13:08:10.78834+00:00
-- url     : https://prove2.me/theorems/e942a052-15b5-45ae-aeed-b1696e5b47fb
-- title:
--   Theorem 5.3 — max k-cover is not approximable within 1 − 1/e + ε unless P = NP
-- statement:
--   Assume the cited Theorem 2.1.1 (gap NP-hardness of MAX 3SAT-B) and the consequence of Raz's parallel repetition theorem (Theorem 2.2.2) stated on p. 642. Let $\varepsilon>0$. If some polynomial-time algorithm, on every max $k$-cover instance, outputs a number $v$ with
--   $$\Big(1-\frac1e+\varepsilon\Big)\mathrm{opt}\ \le\ v\ \le\ \mathrm{opt},$$
--   then $\mathrm{P}=\mathrm{NP}$.
--
--   In the paper's words: for any $\varepsilon > 0$, max $k$-cover cannot be approximated in polynomial time within a ratio of $(1 - 1/e + \varepsilon)$, unless $\mathrm{P} = \mathrm{NP}$. The approximation here only has to output a number, not a collection of sets, which makes the theorem stronger than its constructive version (Proposition 5.2). With Proposition 5.1 (greedy achieves $1-1/e$) it shows that $1-1/e$ is the approximation threshold of max $k$-cover.
--
--   **Formalization Note** $\mathrm{P}$ and $\mathrm{NP}$ are the classes of languages over the binary alphabet for Cook's one-tape Turing machines, so the conclusion contradicts `CookPvsNP.P_ne_NP`. The two cited results enter as the hypotheses `Thm211` and `RazRepetition`. For $\varepsilon>1/e$ the ratio exceeds $1$ and no algorithm satisfies the hypothesis on an instance with $\mathrm{opt}>0$, so those values of $\varepsilon$ are vacuous, as they are in the paper.
-- source:
--   Feige, A threshold of ln n for approximating set cover, J. ACM 45(4) (1998), p. 648, Theorem 5.3

import Mathlib
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_SetCoverThreshold_MaxCover_Formula
import Definitions.Def_SetCoverThreshold_MaxCover_ProofSystem
import Definitions.Def_SetCoverThreshold_MaxCover_Instance

namespace SetCoverThreshold.MaxCover

open CookPvsNP

/-- **Theorem 5.3** (Feige 1998, p. 648): for any `ε > 0`, max k-cover cannot be approximated in
polynomial time within a ratio of `1 − 1/e + ε`, unless `P = NP`; conditional on the cited
Theorem 2.1.1 and the cited parallel repetition bound (Theorem 2.2.2 through its p. 642
consequence). -/
theorem max_k_cover_threshold (h211 : Thm211) (hRaz : RazRepetition) (ε : ℝ) (hε : 0 < ε)
    (hA : MaxCoverApproximable (1 - Real.exp (-1) + ε)) :
    P Bool = NP Bool := by sorry

end SetCoverThreshold.MaxCover
