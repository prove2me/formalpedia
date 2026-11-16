-- Prove2me | Theorems.Thm_VAS5Reach_Supplement_theorem_1_5
-- name    : VAS5Reach.Supplement.theorem_1_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T02:50:34.514196+00:00
-- url     : https://prove2.me/theorems/7f199b05-9644-4bc2-b50e-fc333e170792
-- title:
--   Theorem 1.5 — reachability in $(d+3)$-VAS is in $\mathbf F_d$ for every $d\ge3$, even under binary encoding
-- statement:
--   For every fixed $d\ge3$, the reachability problem for $(d+3)$-VAS under binary encoding lies in the fast-growing complexity class
--   $$\mathbf F_d=\bigcup_{p\in\mathscr F_{<d}}\mathrm{DTIME}\big(F_d(p(n))\big).$$
--
--   For comparison, the best known bound for $d$-VASS reachability is $\mathbf F_d$, so three extra counters of a VAS cost nothing; in particular 6-VAS reachability is in $\mathbf F_3$ (TOWER).
--
--   **Formalization Note** Membership in $\mathbf F_d$ is stated as: a deterministic machine decides the binary-coded language `reachLangBin (d+3)` within $F_d(F_{d-1}^{\,c}(n))$ steps for some $c$.
--
--   Differences from the source:
--   - encoding: 𝐅_d = ⋃_{p ∈ ℱ_{<d}} DTIME(F_d(p(n))) (Schmitz [Sch16, §2]) → ∃ c, a deterministic machine decides the language within F_d(F_{d−1}^c(n)) steps on inputs of length n (InFastGrowingClass d); reason: for d ≥ 3, ℱ_{<d} = ℱ_{d−1}; every p ∈ ℱ_{d−1} is majorized by an iterate F_{d−1}^c and every iterate lies in ℱ_{d−1} (Löb–Wainer), and DTIME is monotone in its bound, so the two unions are the same class
--   - encoding: DTIME on deterministic multitape Turing machines → DecidesInTime on a deterministic machine of the published SpaceMachine model (multitape, read-only input tape), counting steps until it halts; reason: a multitape Turing machine with a read-only input tape; the time classes F_d(F_{d−1}^c(n)) are insensitive to the linear and polynomial overheads between multitape variants
--   - encoding: binary encoding of a (d+3)-VAS instance → reachLangBin (d + 3) (sign bit + binary digits per integer, self-delimiting fields); reason: any standard binary code; 𝐅_d is closed under the elementary conversions between codes
-- source:
--   Chen, Fu, Fu, Reachability in Five-Dimensional Vector Addition Systems Is PSPACE-Complete, arXiv:2610.40012 (held version, sha256 a74d76f9…), Theorem 1.5, p.3 (PDF p.5); restated and proved App. A.3, p.45 (PDF p.47); 𝐅_d as in [Sch16, Section 2]

import Mathlib
import Definitions.Def_VAS5Reach_Supplement_reachLang
import Definitions.Def_VAS5Reach_Supplement_fastGrowing

namespace VAS5Reach.Supplement

/-- **Theorem 1.5.** Reachability in `(d + 3)`-VAS is in `𝐅_d` for every fixed `d ≥ 3`, even under
binary encoding.

Source: W. Chen, B. Fu, Y. Fu, *Reachability in Five-Dimensional Vector Addition Systems Is
PSPACE-Complete*, arXiv:2610.40012 (held version, sha256 a74d76f9…), Theorem 1.5, printed p. 3
(PDF p. 5); restated and proved in App. A.3, printed p. 45 (PDF p. 47), with `𝐅_d` as in
[Sch16, Section 2] (S. Schmitz, *Complexity hierarchies beyond elementary*, ACM TOCT 8(1), 2016).

**Formalization Note** The language is `(d+3)`-VAS reachability with all numbers in binary
(`reachLangBin (d + 3)`). `𝐅_d = ⋃_{p ∈ ℱ_{<d}} DTIME(F_d(p(n)))` is stated through the iterates
`F_{d−1}^c`, which majorize `ℱ_{<d} = ℱ_{d−1}` (`InFastGrowingClass`). -/
theorem theorem_1_5 (d : ℕ) (hd : 3 ≤ d) : InFastGrowingClass d (reachLangBin (d + 3)) := by sorry

end VAS5Reach.Supplement
