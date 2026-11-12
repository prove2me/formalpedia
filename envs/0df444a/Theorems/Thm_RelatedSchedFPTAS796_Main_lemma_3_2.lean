-- Prove2me | Theorems.Thm_RelatedSchedFPTAS796_Main_lemma_3_2
-- name    : RelatedSchedFPTAS796.Main.lemma_3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T07:14:42.85934+00:00
-- url     : https://prove2.me/theorems/82ec1054-6126-457f-b4fc-56770b716536
-- title:
--   Lemma 3.2 — a complete-profile solver gives an $\tilde O(n+(1/\varepsilon)^{m-1})$-time randomized FPTAS for $Qm\|C_{\max}$
-- statement:
--   There is an $\tilde O(n+(1/\varepsilon)^{m-1})$-time randomized FPTAS for $Qm\|C_{\max}$ if any complete-profile problem $(J,t,q)$ can be approximately solved in $\tilde O(|J|+(1/\varepsilon)^{m-1})$ time. Formally, for $m\ge1$:
--   $$\text{CompleteProfileSolvable}(m)\ \Longrightarrow\ \text{RandomizedFPTAS}(m).$$
--   The conclusion is the goal's predicate: one program that, for every instance with $n\ge0$ positive rational sizes and $m$ positive rational speeds, every rational $\varepsilon,q\in(0,1)$ and every admissible word width, halts on every coin sequence within $C(n+(1/\varepsilon)^{m-1})(\log_2(n+2)\log_2(2/\varepsilon)\log_2(2/q))^c$ steps and with probability at least $1-q$ outputs a schedule of makespan at most $(1+\varepsilon)\mathrm{OPT}$.
--
--   Combined with Lemma 5.9 it proves Theorem 1.1.
--
--   Differences from the source:
--   - reading: "can be approximately solved in time" on "the standard word RAM model" → one program of the published randomized word RAM at every width $w\ge b(\lfloor\log_2(|J|+M+2)\rfloor+1)$; time worst case over the coins, approximation with probability $\ge1-q$, output size on every run; reason: the paper names no machine; trans-dichotomous convention; the size bound of Definitions 3.1/3.3 is read as unconditional
--   - reading: "$O(1/\varepsilon)$ jobs", "$t_i=O(1/\varepsilon^2)$", "$\kappa_d=O(1/\varepsilon)$" → for every constant $a$: $|J|\le a/\varepsilon$, $t_i\le a/\varepsilon^2$, $\kappa_d\le a/\varepsilon$, with the program and its constants depending on $a$; reason: the strongest reading of the hidden constants; it is what the reductions of Appendix C produce
--   - encoding: $1/\varepsilon$ a power of two (p.7, the convention of §§3–5) → $\varepsilon=2^{-\ell}$ with $\ell\ge1$, given as the word $\ell$; reason: the paper's own convention for these sections; $\varepsilon<1$
--   - encoding: $\tilde O(X)$, suppressing factors polynomial in $\log(|J|+2)$, $\log(2/\varepsilon)$, $\log(2/q)$, constants depending on the dimension → $C\cdot X\cdot(\log_2(|J|+2)\log_2(2/\varepsilon)\log_2(2/q))^c$ with $C,c\in\mathbb N$ fixed before the instance; reason: the paper's definition of $\tilde O$ (p.7)
--   - reading: "randomized FPTAS": guarantee with probability at least $1-q$, time polynomial also in $\log(1/q)$ (p.8) → the failure parameter $q$ is an input and $\log_2(2/q)$ enters the $\tilde O$ factor; reason: the paper's own definition (p.8) and $\tilde O$ convention (p.7)
--   - encoding: the output is a schedule → cell $j$ holds the $0$-based machine of job $j+1$; $C_{\max}(\sigma)\le(1+\varepsilon)C_{\max}(\tau)$ for every $\tau$; reason: equivalent to $C_{\max}(\sigma)\le(1+\varepsilon)\mathrm{OPT}$ since the minimum over the $m^n$ schedules is attained
--   - generalization: the hypothesis "any complete-profile problem $(J,t,q)$ can be approximately solved" (the proof, Appendix C p.28, calls it on the $k\le m$ retained machines of each class) → the hypothesis only for complete-profile instances on exactly $m$ machines; reason: a weaker hypothesis gives a stronger implication; the source's hypothesis implies the $m$-machine one, so the Lean statement specializes to the source's; a $k$-machine instance embeds into $m$ machines by adding $m-k$ machines with a positive target too small to hold a job of size $\ge1/\varepsilon$ even after the additive error
-- source:
--   Lin Chen, Tingwei Hu, Jiayi Lian, Yuchen Mao, Guochuan Zhang, Faster Approximation Schemes for Scheduling on Related Machines, STOC 2027 submission #796 (October 2026), source.pdf SHA-256 5d7d0135eed9cbe942c80598e2bb07d8c56ab67aec0d6e8486a067237654f7f3, p.9, Lemma 3.2 (proof Appendix C, pp.28–29); FPTAS definition p.8 lines 285–287

import Mathlib
import Definitions.Def_MatroidSensOracle_WordRAM
import Definitions.Def_RelatedSchedFPTAS796_Main_Model
import Definitions.Def_RelatedSchedFPTAS796_Main_Machine
import Definitions.Def_RelatedSchedFPTAS796_Main_Problems

set_option autoImplicit false

open MatroidSensOracle MeasureTheory Pointwise

namespace RelatedSchedFPTAS796.Main

/-- **Lemma 3.2**, p.9 (proof Appendix C, pp.28–29). There is an `Õ(n + (1/ε)^{m−1})`-time
randomized FPTAS for `Qm∥Cmax` if any complete-profile problem `(J, t, q)` (on `m` machines,
Definition 3.1) can be approximately solved in `Õ(|J| + (1/ε)^{m−1})` time. -/
theorem lemma_3_2 (m : ℕ) (hm : 1 ≤ m) (h : CompleteProfileSolvable m) :
    RandomizedFPTAS m := by sorry

end RelatedSchedFPTAS796.Main
