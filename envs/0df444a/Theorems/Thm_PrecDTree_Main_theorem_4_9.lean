-- Prove2me | Theorems.Thm_PrecDTree_Main_theorem_4_9
-- name    : PrecDTree.Main.theorem_4_9
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T03:53:04.211024+00:00
-- url     : https://prove2.me/theorems/2c2d5bf9-67b8-41e2-9257-357b7ad00ebf
-- title:
--   Theorem 4.9 — a polynomial-time (O(m^{1/3}), 8)-approximation for f-PCSC
-- statement:
--   There is a polynomial-time $(O(m^{1/3}),8)$-approximation algorithm for f-PCSC: for a universal constant $C>0$, one polynomial-time machine outputs on every f-PCSC instance (a family of $m$ sets with universe $U$, $n=|U|$, a partial order on the sets, $0<f\le1$) a precedence-closed family $\mathcal C$ with
--   $$|\mathrm{cov}(\mathcal C)|\ \ge\ \frac{f\cdot n}{8}\qquad\text{and}\qquad|\mathcal C|\ \le\ C\cdot m^{1/3}\cdot\mathrm{OPT}.$$
--   Fed to Theorem 3.8 as FindCover, it gives Corollary 4.10.
--
--   Differences from the source:
--   - reading: polynomial-time algorithm (no machine model named) → one Mathlib Turing.TM2ComputableInPolyTime machine on binary words (PolyTimeBin), fixed before the instance, required to behave only on codes of valid instances; reason: the standard formal reading of a polynomial-time algorithm; the codes (encNat, incidence bits, tables) are of length polynomial in the input size
--   - reading: O(·) → an explicit universal constant C > 0, quantified before the algorithm and every instance; reason: 'O(g)-approximation' means cost ≤ C · g · OPT with C independent of the instance
--   - encoding: 0 < f ≤ 1 real in an f-PCSC instance → f rational in the encoded instance (PCSCInstance.f : ℚ); reason: an algorithm's input is finite; a real f has the same feasible families and the same OPT as the rational f' = ⌈f·n⌉/n, and the guarantee f'·n/8 ≥ f·n/8 for f' implies the one for f
--   - encoding: a universe U of n items and a family S of m subsets of U with ⋃S = U (p. 1) → sets : Fin m → Finset (Fin N), universe coverUniverse sets = ⋃ sets, n = |⋃ sets|; reason: the paper's convention ⋃_{S∈S} S = U (p. 1); the family is indexed, as ξ(T) is (p. 6)
-- source:
--   Szyfelbein, Dereniowski, Precedence-Constrained Decision Trees and Coverings, arXiv:2602.21312 (STOC 2027 submission version, sha256 aafd336d…), p. 17, Theorem 4.9

import Mathlib
import Definitions.Def_PrecDTree_Main_Machine

set_option autoImplicit false

namespace PrecDTree.Main

/-- **Theorem 4.9** (p. 17). There is a polynomial-time `(O(m^{1/3}), 8)`-approximation algorithm
for f-PCSC: for a universal constant `C > 0`, a bicriteria `(C · m^{1/3}, 8)`-approximation. -/
theorem theorem_4_9 :
    ∃ C : ℝ, 0 < C ∧ HasPolyPCSCApprox (fun m => C * (m : ℝ) ^ ((1 : ℝ) / 3)) 8 := by sorry

end PrecDTree.Main
