-- Prove2me | Theorems.Thm_RelatedSchedFPTAS796_Main_theorem_1_1_randomized_fptas
-- name    : RelatedSchedFPTAS796.Main.theorem_1_1_randomized_fptas
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T07:14:52.374811+00:00
-- url     : https://prove2.me/theorems/8c0dba18-ecdf-496c-926d-b666c7a95f89
-- title:
--   Theorem 1.1 — a randomized FPTAS for $Qm\|C_{\max}$ in $\tilde O(n+(1/\varepsilon)^{m-1})$ time
-- statement:
--   For every fixed $m\ge1$ there is a randomized FPTAS for makespan minimization on $m$ uniformly related machines ($Qm\|C_{\max}$) running in $\tilde O(n+(1/\varepsilon)^{m-1})$ time.
--
--   Precisely, there are a program $P$ of the randomized word RAM and constants $b,C,c\in\mathbb N$, depending only on $m$, such that for every $n\ge0$, all positive rational job sizes $p_1,\dots,p_n$ and machine speeds $s_1,\dots,s_m$, all rationals $\varepsilon,q\in(0,1)$ and every word width $w\ge b(\lfloor\log_2(n+M+2)\rfloor+1)$ ($M$ the largest input word):
--
--   1. on every coin sequence, $P$ halts within
--   $$C\,\big(n+(1/\varepsilon)^{m-1}\big)\,\big(\log_2(n+2)\cdot\log_2(2/\varepsilon)\cdot\log_2(2/q)\big)^c$$
--   steps; and
--   2. with probability at least $1-q$ it halts within that bound with a schedule $\sigma$ written in its output cells satisfying
--   $$C_{\max}(\sigma)\ \le\ (1+\varepsilon)\,\mathrm{OPT},$$
--   where $C_{\max}(\sigma)=\max_iL_i(\sigma)$, $L_i(\sigma)=\frac1{s_i}\sum_{j:\sigma(j)=i}p_j$, and $\mathrm{OPT}$ is the minimum makespan over all $m^n$ schedules.
--
--   The input words are $n$, the speeds, the sizes, $\varepsilon$ and $q$ (each rational as numerator and denominator); cell $j-1$ of the output holds the $0$-based machine of job $j$.
--
--   The printed success probability follows: for a fixed $c'$ and $n\ge1$, run $P$ with $q=(\varepsilon/(n+1))^{c'}$; then $\log_2(2/q)\le(c'+1)\log_2(n+2)\log_2(2/\varepsilon)$, so the time is $\tilde O(n+(1/\varepsilon)^{m-1})$ with $\tilde O$ suppressing factors polynomial in $\log(n+2)$ and $\log(2/\varepsilon)$, and the success probability is at least $1-(n/\varepsilon)^{-c'}$.
--
--   Compared with the $O(n)+(m/\varepsilon)^{O(m)}$ scheme of Jansen and Mastrolilli, the exponent of $1/\varepsilon$ is the explicit $m-1$ while the dependence on $n$ stays near-linear.
--
--   **Formalization Note** The statement is `RandomizedFPTAS m` from the definition item `Problems`: one program for all instances, worst-case time on every coin sequence, and the failure probability measured by the coin law. Approximation is against the true optimum over all schedules, and $\varepsilon$ is any rational in $(0,1)$, not only an inverse power of two.
--
--   Differences from the source:
--   - generalization: success probability at least $1-(n/\varepsilon)^{-O(1)}$ → a failure parameter $q\in(0,1)$ as input, success probability $\ge1-q$, and $\log_2(2/q)$ in the polylogarithmic factor; reason: the paper's definition of a randomized FPTAS (p.8); $q=(\varepsilon/(n+1))^{c'}$ gives $1-(n/\varepsilon)^{-c'}$ for every fixed $c'$ and $n\ge1$ within the printed time bound
--   - reading: "the standard word RAM model" (p.7), no instruction set named → one program of the published randomized word RAM `MatroidSensOracle` (unit cost, $w$-bit words, uniform coins), required at every width $w\ge b(\lfloor\log_2(n+M+2)\rfloor+1)$; time worst case over all coin sequences; reason: the trans-dichotomous convention under which a bound independent of the bit length is meaningful; no unit-cost unbounded arithmetic and no width growing with $n$
--   - encoding: $\tilde O(\cdot)$ suppressing factors polynomial in $\log(n+2)$, $\log(2/\varepsilon)$, constants depending on $m$ → $C(n+(1/\varepsilon)^{m-1})(\log_2(n+2)\log_2(2/\varepsilon)\log_2(2/q))^c$ with $C,c$ fixed with the program; reason: the paper's definition of $\tilde O$ (p.3, p.7)
--   - encoding: positive rational sizes and speeds, a schedule as output → each rational as the words numerator, denominator; the schedule in cells $0,\dots,n-1$ as $0$-based machine indices; $C_{\max}(\sigma)\le(1+\varepsilon)C_{\max}(\tau)$ for every $\tau$; reason: standard input encoding; equivalent to $C_{\max}(\sigma)\le(1+\varepsilon)\mathrm{OPT}$ since the minimum is attained
-- source:
--   Lin Chen, Tingwei Hu, Jiayi Lian, Yuchen Mao, Guochuan Zhang, Faster Approximation Schemes for Scheduling on Related Machines, STOC 2027 submission #796 (October 2026), source.pdf SHA-256 5d7d0135eed9cbe942c80598e2bb07d8c56ab67aec0d6e8486a067237654f7f3, p.3, Theorem 1.1 and lines 86–87; proof p.18 lines 634–635; FPTAS definition p.8 lines 285–287

import Mathlib
import Definitions.Def_MatroidSensOracle_WordRAM
import Definitions.Def_RelatedSchedFPTAS796_Main_Model
import Definitions.Def_RelatedSchedFPTAS796_Main_Machine
import Definitions.Def_RelatedSchedFPTAS796_Main_Problems

set_option autoImplicit false

open MatroidSensOracle MeasureTheory Pointwise

namespace RelatedSchedFPTAS796.Main

/-- **Theorem 1.1**, p.3 (proof p.18 lines 634–635). For every fixed `m ≥ 1` there is a randomized
FPTAS for `Qm∥Cmax` in `Õ(n + (1/ε)^{m−1})` time: one program of the randomized word RAM and
constants `b, C, c` (depending on `m` only) such that for every instance with `n ≥ 0` positive
rational job sizes and `m` positive rational speeds, every rational `ε, q ∈ (0, 1)` and every word
width `w ≥ b(⌊log₂(n + M + 2)⌋ + 1)`, the run halts on every coin sequence within
`C(n + (1/ε)^{m−1})(log₂(n+2)·log₂(2/ε)·log₂(2/q))^c` steps, and with probability at least `1 − q`
it outputs a schedule of makespan at most `(1 + ε)·OPT` (`RandomizedFPTAS`). Taking
`q = (ε/(n+1))^{c'}` gives the printed success probability `1 − (n/ε)^{−O(1)}`. -/
theorem theorem_1_1_randomized_fptas (m : ℕ) (hm : 1 ≤ m) : RandomizedFPTAS m := by sorry

end RelatedSchedFPTAS796.Main
