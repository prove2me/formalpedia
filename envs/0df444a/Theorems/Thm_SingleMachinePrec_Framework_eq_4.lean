-- Prove2me | Theorems.Thm_SingleMachinePrec_Framework_eq_4
-- name    : SingleMachinePrec.Framework.eq_4
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T14:06:58.340992+00:00
-- url     : https://prove2.me/theorems/c18b2c45-837c-4492-a155-eba0effc8255
-- title:
--   Eq. (4) — each incomparable pair is reversed with probability at least k/t under a uniform draw from a k : t-realizer
-- statement:
--   Let $L_1,\dots,L_t$ be a $k:t$-realizer of the relation $P$ and draw an index $i$ uniformly from $\{1,\dots,t\}$. For every incomparable pair $(x,y)$, the probability that $L_i$ reverses it is at least $k/t$:
--   $$\frac1t\,\bigl|\{i = 1,\dots,t : y < x \text{ in } L_i\}\bigr| \;\ge\; \frac kt.$$
--
--   This is the per-pair estimate that, by linearity of expectation, gives Eq. (5).
--
--   **Formalization Note** The probability is written as the uniform average over the indices $i \in \{1,\dots,t\}$. The page writes the event as "$y > x$ in $L_i$" while the realizer counts $y < x$; since $\operatorname{inc}(P)$ is closed under swapping, the two readings are the same family of inequalities, and the statement uses the reversal convention of §2.1 throughout.
-- source:
--   Ambühl, Mastrolilli, Mutsanas, Svensson, On the Approximability of Single-Machine Scheduling with Precedence Constraints, Math. Oper. Res. 36(4) (2011), p. 659, Eq. (4) (proof of Theorem 5.1)

import Mathlib
import Definitions.Def_SingleMachinePrec_Framework_Poset

namespace SingleMachinePrec.Framework

open Classical in
/-- **Eq. (4)** (p. 659). If `L_1, …, L_t` is a `k : t`-realizer of `P`, then for every
incomparable pair `u` the fraction of the `L_i` that reverse `u` is at least `k / t`. -/
theorem eq_4 {N : Type*} [Fintype N] (P : N → N → Prop) (k t : ℕ)
    (L : Fin t → LinearExtension P) (hL : IsKFoldRealizer P k t L) (u : IncPair P) :
    (k : ℝ) / t ≤ (1 / (t : ℝ)) * (Finset.univ.filter (fun i => (L i).Reverses u)).card := by sorry

end SingleMachinePrec.Framework
