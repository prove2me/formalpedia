-- Prove2me | Theorems.Thm_RelatedSchedFPTAS796_Main_lemma_3_4
-- name    : RelatedSchedFPTAS796.Main.lemma_3_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T07:14:41.85661+00:00
-- url     : https://prove2.me/theorems/427c72d2-c89f-4032-9689-530a85b955ec
-- title:
--   Lemma 3.4 — partial-profile solvers in dimensions $\le m-1$ give a complete-profile solver on $m$ machines
-- statement:
--   If the partial-profile problem in dimension $d$ can be approximately solved in $\tilde O(|J|+(1/\varepsilon)^d)$ time, then the complete-profile problem on $m$ machines can be approximately solved in $\tilde O(|J|+(1/\varepsilon)^{m-1})$ time. Formally, for $m\ge1$:
--   $$\big(\forall d\in\{1,\dots,m-1\}:\ \text{PartialProfileSolvable}(d)\big)\ \Longrightarrow\ \text{CompleteProfileSolvable}(m),$$
--   with both predicates as in Definitions 3.1 and 3.3 on the randomized word RAM (time worst case, output size $\tilde O$ on every run, approximation with probability at least $1-q$, every admissibility constant).
--
--   Together with Algorithm 1 and Lemma 5.8, it carries the induction on the number of machines in Lemma 5.9.
--
--   Differences from the source:
--   - reading: "the partial-profile problem in dimension $d$" → the partial-profile problem in every dimension $1\le d\le m-1$; reason: the reduction calls dimensions up to $m-1$ (p.30: "Each call has dimension at most $m-1$")
--   - reading: "can be approximately solved in time" on "the standard word RAM model" → one program of the published randomized word RAM at every width $w\ge b(\lfloor\log_2(|J|+M+2)\rfloor+1)$; time worst case over the coins, approximation with probability $\ge1-q$, output size on every run; reason: the paper names no machine; trans-dichotomous convention; the size bound of Definitions 3.1/3.3 is read as unconditional
--   - reading: "$O(1/\varepsilon)$ jobs", "$t_i=O(1/\varepsilon^2)$", "$\kappa_d=O(1/\varepsilon)$" → for every constant $a$: $|J|\le a/\varepsilon$, $t_i\le a/\varepsilon^2$, $\kappa_d\le a/\varepsilon$, with the program and its constants depending on $a$; reason: the strongest reading of the hidden constants; it is what the reductions of Appendix C produce
--   - encoding: $1/\varepsilon$ a power of two (p.7, the convention of §§3–5) → $\varepsilon=2^{-\ell}$ with $\ell\ge1$, given as the word $\ell$; reason: the paper's own convention for these sections; $\varepsilon<1$
--   - encoding: $\tilde O(X)$, suppressing factors polynomial in $\log(|J|+2)$, $\log(2/\varepsilon)$, $\log(2/q)$, constants depending on the dimension → $C\cdot X\cdot(\log_2(|J|+2)\log_2(2/\varepsilon)\log_2(2/q))^c$ with $C,c\in\mathbb N$ fixed before the instance; reason: the paper's definition of $\tilde O$ (p.7)
-- source:
--   Lin Chen, Tingwei Hu, Jiayi Lian, Yuchen Mao, Guochuan Zhang, Faster Approximation Schemes for Scheduling on Related Machines, STOC 2027 submission #796 (October 2026), source.pdf SHA-256 5d7d0135eed9cbe942c80598e2bb07d8c56ab67aec0d6e8486a067237654f7f3, p.10, Lemma 3.4 (proof Appendix C, pp.29–30)

import Mathlib
import Definitions.Def_MatroidSensOracle_WordRAM
import Definitions.Def_RelatedSchedFPTAS796_Main_Model
import Definitions.Def_RelatedSchedFPTAS796_Main_Machine
import Definitions.Def_RelatedSchedFPTAS796_Main_Problems

set_option autoImplicit false

open MatroidSensOracle MeasureTheory Pointwise

namespace RelatedSchedFPTAS796.Main

/-- **Lemma 3.4**, p.10 (proof Appendix C, pp.29–30). If the partial-profile problem in dimension
`d` can be approximately solved in `Õ(|J| + (1/ε)^d)` time (for each dimension `1 ≤ d ≤ m − 1`),
then the complete-profile problem on `m` machines can be approximately solved in
`Õ(|J| + (1/ε)^{m−1})` time. -/
theorem lemma_3_4 (m : ℕ) (hm : 1 ≤ m)
    (h : ∀ d : ℕ, 1 ≤ d → d ≤ m - 1 → PartialProfileSolvable d) :
    CompleteProfileSolvable m := by sorry

end RelatedSchedFPTAS796.Main
