-- Prove2me | Theorems.Thm_PrecDTree_Main_theorem_4_2
-- name    : PrecDTree.Main.theorem_4_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T03:53:02.09001+00:00
-- url     : https://prove2.me/theorems/53c6c918-20d2-4766-afe4-29f60fb2c122
-- title:
--   Theorem 4.2 — a polynomial-time bicriteria algorithm for Partial-RBSC: blue coverage ≥ t/8, red cost ≤ 920 · m^{1/3} · OPT
-- statement:
--   For an instance $I=(R,B,\mathcal S,t)$ of Partial-RBSC with $m=|\mathcal S|$ there is a polynomial-time algorithm that outputs a cover $\mathcal C\subseteq\mathcal S$ satisfying
--   $$|\mathrm{cov}(\mathcal C,B)|\ \ge\ t/8\qquad\text{and}\qquad|\mathrm{cov}(\mathcal C,R)|\ \le\ 920\cdot m^{1/3}\cdot\mathrm{OPT}(I).$$
--   One machine serves every feasible instance ($|\mathrm{cov}(\mathcal S,B)|\ge t$). The red cost bound improves the $O(m^{1/3}\log^{4/3}k\log n)$ of Chlamtáč, Makarychev and Vakilian at the price of a constant-factor loss in coverage; via the reduction of §4.2 it yields Theorem 4.9.
--
--   **Formalization Note.** $t/8$ is a rational number (no rounding), and $m^{1/3}$ the real cube root.
--
--   Differences from the source:
--   - reading: polynomial-time algorithm (no machine model named) → one Mathlib Turing.TM2ComputableInPolyTime machine on binary words (PolyTimeBin), fixed before the instance, required to behave only on codes of valid instances; reason: the standard formal reading of a polynomial-time algorithm; the codes (encNat, incidence bits, tables) are of length polynomial in the input size
--   - encoding: an integer target t → t : ℕ; reason: a negative target has the same feasible covers, the same OPT (= 0) and the same output condition as t = 0
--   - reading: an instance of Partial-RBSC → the guarantee is required on feasible instances (|cov(S, B)| ≥ t); reason: OPT(I) exists only on feasible instances
--   - encoding: disjoint sets R, B and subsets of R ∪ B → R = Fin k, B = Fin n (disjoint by typing), each set given by its red part and its blue part; reason: a subset of R ∪ B is exactly the pair of its red and blue parts
-- source:
--   Szyfelbein, Dereniowski, Precedence-Constrained Decision Trees and Coverings, arXiv:2602.21312 (STOC 2027 submission version, sha256 aafd336d…), p. 9, Theorem 4.2

import Mathlib
import Definitions.Def_PrecDTree_Main_Machine

set_option autoImplicit false

namespace PrecDTree.Main

/-- **Theorem 4.2** (p. 9). For an instance `I = (R, B, S, t)` of Partial-RBSC there is a
polynomial-time algorithm that outputs a cover `C ⊆ S` with `|cov(C, B)| ≥ t/8` and
`|cov(C, R)| ≤ 920 · m^{1/3} · OPT(I)`. One machine serves every feasible instance. -/
theorem theorem_4_2 :
    ∃ alg : List Bool → List Bool, PolyTimeBin alg ∧
      ∀ I : RBInstance, I.Feasible →
        ∃ C : Finset (Fin I.m), alg (encodeRB I) = encodeFamily C ∧
          (I.t : ℝ) / 8 ≤ ((I.blueCov C).card : ℝ) ∧
          ((I.redCov C).card : ℝ) ≤ 920 * (I.m : ℝ) ^ ((1 : ℝ) / 3) * (I.opt : ℝ) := by sorry

end PrecDTree.Main
