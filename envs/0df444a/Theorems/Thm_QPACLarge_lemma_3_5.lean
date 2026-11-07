-- Prove2me | Theorems.Thm_QPACLarge_lemma_3_5
-- name    : QPACLarge.lemma_3_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:08:51.548666+00:00
-- url     : https://prove2.me/theorems/4365564e-52b1-4a2b-8ad1-664352fde1e3
-- title:
--   Lemma 3.5 — majority of $m$ independent signs of mean $1/\sqrt N$ has mean $\ge b\sqrt{m/N}$
-- statement:
--   There is a universal constant $0 < b \le 1$ such that for every $n \ge 1$, $N = 2^n$, and every odd $m$ with $1 \le m \le N$, independent signs $B_1, \dots, B_m \in \{-1,+1\}$ of mean $1/\sqrt N$ satisfy
--
--   $$
--   \mathbb E[\mathrm{Sign}(B_1, \dots, B_m)] \ge b\sqrt{\frac mN},
--   $$
--
--   where $\mathrm{Sign}$ is the sign of the sum. The paper cites this from [Wat20, Appendix A] without proof.
--
--   Differences from the source:
--   - encoding: independent signs of mean $1/\sqrt N$ → the product law with $\Pr[B_i = b] = (1 + b/\sqrt N)/2$; reason: this is the only law of a $\pm1$ variable with mean $1/\sqrt N$
--   - reading: $N$ → $N = 2^n$ with $n \ge 1$; reason: Section 2.1: "For a given $n \ge 1$ we will implicitly use $N = 2^n$"
-- source:
--   Oliveira, Unconditional Quantum PAC Learning Advantage in the Large Error Regime, arXiv:2610.23268 (held file sha256 e749e7c9…), Lemma 3.5, p.28

import Mathlib
import Definitions.Def_QPACLarge_IsMajorityBiasConst

namespace QPACLarge

/-- **Lemma 3.5 (Majority Bias; see [Wat20, Appendix A]).**
Oliveira, *Unconditional Quantum PAC Learning Advantage in the Large Error Regime*, arXiv:2610.23268 (held file sha256 e749e7c9…), Lemma 3.5, p.28: "There is a universal constant `0 < b ≤ 1` such that, for every odd integer
`m` with `1 ≤ m ≤ N`, independent signs `B₁, …, B_m ∈ {−1, +1}` of mean `1/√N` satisfy
`E[Sign(B₁, …, B_m)] ≥ b √(m/N)`, where `Sign(B₁, …, B_m) ∈ {−1, +1}` denotes the sign of their
sum."

**Formalization Note.** `N = 2ⁿ` with `n ≥ 1` (Section 2.1, p.14); see `IsMajorityBiasConst`. The
paper cites the proof and gives none. -/
theorem lemma_3_5 : ∃ b : ℝ, IsMajorityBiasConst b := by sorry

end QPACLarge
