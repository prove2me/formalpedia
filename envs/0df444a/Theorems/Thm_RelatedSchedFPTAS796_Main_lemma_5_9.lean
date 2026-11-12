-- Prove2me | Theorems.Thm_RelatedSchedFPTAS796_Main_lemma_5_9
-- name    : RelatedSchedFPTAS796.Main.lemma_5_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T07:14:38.056648+00:00
-- url     : https://prove2.me/theorems/7faec5f0-8bf5-4e4a-8427-43643cb87f1e
-- title:
--   Lemma 5.9 — every admissible complete-profile instance on $m\ge1$ machines is approximately solved in $\tilde O(|J|+(1/\varepsilon)^{m-1})$
-- statement:
--   Every admissible complete-profile instance $(J,t,q)$ on $m\ge1$ machines can be approximately solved in $\tilde O(|J|+(1/\varepsilon)^{m-1})$ time:
--   $$\text{CompleteProfileSolvable}(m)\qquad(m\ge1).$$
--   That is, for every admissibility constant $a$ there are a randomized word-RAM program and constants $b,C,c$ such that on every instance with $\varepsilon=2^{-\ell}$, $J\subseteq[1/\varepsilon,2/\varepsilon)\cap\mathbb Z$, $|J|\le a/\varepsilon$, $0<t_i\le a/\varepsilon^2$, $q\in(0,1)$, and every admissible width, the run halts within $C(|J|+(1/\varepsilon)^{m-1})\,\mathrm{polylog}$ steps with at most $C(1/\varepsilon)^{m-1}\mathrm{polylog}$ output vectors, and with probability at least $1-q$ the output approximates $\mathcal P(J,[0,t])$ with additive error $C\varepsilon t_i\,\mathrm{polylog}$.
--
--   Combined with Lemma 3.2 it proves Theorem 1.1.
--
--   Differences from the source:
--   - reading: "can be approximately solved in time" on "the standard word RAM model" → one program of the published randomized word RAM at every width $w\ge b(\lfloor\log_2(|J|+M+2)\rfloor+1)$; time worst case over the coins, approximation with probability $\ge1-q$, output size on every run; reason: the paper names no machine; trans-dichotomous convention; the size bound of Definitions 3.1/3.3 is read as unconditional
--   - reading: "$O(1/\varepsilon)$ jobs", "$t_i=O(1/\varepsilon^2)$", "$\kappa_d=O(1/\varepsilon)$" → for every constant $a$: $|J|\le a/\varepsilon$, $t_i\le a/\varepsilon^2$, $\kappa_d\le a/\varepsilon$, with the program and its constants depending on $a$; reason: the strongest reading of the hidden constants; it is what the reductions of Appendix C produce
--   - encoding: $1/\varepsilon$ a power of two (p.7, the convention of §§3–5) → $\varepsilon=2^{-\ell}$ with $\ell\ge1$, given as the word $\ell$; reason: the paper's own convention for these sections; $\varepsilon<1$
--   - encoding: $\tilde O(X)$, suppressing factors polynomial in $\log(|J|+2)$, $\log(2/\varepsilon)$, $\log(2/q)$, constants depending on the dimension → $C\cdot X\cdot(\log_2(|J|+2)\log_2(2/\varepsilon)\log_2(2/q))^c$ with $C,c\in\mathbb N$ fixed before the instance; reason: the paper's definition of $\tilde O$ (p.7)
-- source:
--   Lin Chen, Tingwei Hu, Jiayi Lian, Yuchen Mao, Guochuan Zhang, Faster Approximation Schemes for Scheduling on Related Machines, STOC 2027 submission #796 (October 2026), source.pdf SHA-256 5d7d0135eed9cbe942c80598e2bb07d8c56ab67aec0d6e8486a067237654f7f3, p.17, Lemma 5.9 (proof pp.17–18)

import Mathlib
import Definitions.Def_MatroidSensOracle_WordRAM
import Definitions.Def_RelatedSchedFPTAS796_Main_Model
import Definitions.Def_RelatedSchedFPTAS796_Main_Machine
import Definitions.Def_RelatedSchedFPTAS796_Main_Problems

set_option autoImplicit false

open MatroidSensOracle MeasureTheory Pointwise

namespace RelatedSchedFPTAS796.Main

/-- **Lemma 5.9**, p.17 (proof pp.17–18). Every admissible complete-profile instance `(J, t, q)` on
`m ≥ 1` machines can be approximately solved in `Õ(|J| + (1/ε)^{m−1})` time. -/
theorem lemma_5_9 (m : ℕ) (hm : 1 ≤ m) : CompleteProfileSolvable m := by sorry

end RelatedSchedFPTAS796.Main
