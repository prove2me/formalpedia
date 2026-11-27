-- Prove2me | Theorems.Thm_TradingPostNSW_Leontief_Supplement_theorem_4_10
-- name    : TradingPostNSW.Leontief.Supplement.theorem_4_10
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-23T20:36:22.684868+00:00
-- url     : https://prove2.me/theorems/d690e9fe-435b-4afd-81eb-e2f488f77be4
-- title:
--   Theorem 4.10, p. 16 — Trading Post with concave valuations has price of anarchy at most 2
-- statement:
--   Let each agent $i$ have a utility $U_i:[0,1]^m\to\mathbb R$ that is concave, non-decreasing and non-negative, and a budget $B_i\ge1$, and assume perfect competition: every good $j$ matters to two distinct agents (each has two bundles differing only in good $j$ with different utilities). Then every pure Nash equilibrium $b$ of the Trading Post game (no fee) satisfies, for every feasible allocation $y$,
--   $$NSW_U(y)\ \le\ 2\,NSW_U\big(x(b)\big),\qquad NSW_U(z)=\Big(\prod_iU_i(z_i)^{B_i}\Big)^{1/B}.$$
--
--   This extends Theorem 4.1 from linear valuations to the general utilities of market equilibrium theory.
--
--   **Formalization Note** The utilities are functions on all of $\mathbb R^m$ in Lean; only their values on the box $[0,1]^m$ are constrained, and only those values are used. The field $v$ of the instance is not used.
--
--   Differences from the source:
--   - encoding: price of anarchy at most c (a maximum of ratios NSW(x*)/NSW(x)) → NSW(y) ≤ c·NSW(x) for every feasible y and every equilibrium outcome x; reason: the multiplicative form avoids dividing by NSW(x); it is the ratio bound with a/0 = ∞
--   - reading: perfect competition: two buyers demand a strictly positive amount of j when it is priced at zero → two distinct agents whose utility depends on good j somewhere on the box; reason: for non-decreasing utilities a buyer demands a free good exactly when it increases utility; p. 12 states that for additive and Leontief valuations the condition is v_{i,j}, v_{k,j} > 0, which this reading reproduces
--   - encoding: the Trading Post allocation x_{i,j} = b_{i,j}/Σ_k b_{k,j} if b_{i,j} > 0, else 0 (p. 12) → the base allocation of TP(0), whose effective bids equal the bids for every b ≥ 0; reason: the same allocation on every strategy profile
--   - reading: Nash equilibrium → pure Nash equilibrium; reason: §2 (p. 6) defines the price of anarchy over the set E of pure Nash equilibria
-- source:
--   Brânzei, Gkatzelis, Mehta, Nash Social Welfare Approximation for Strategic Agents, arXiv:1607.01569v3, p. 16, Theorem 4.10; proof pp. 23–24 (Appendix C)

import Mathlib
import Definitions.Def_TradingPostNSW_Leontief_Setting
import Definitions.Def_TradingPostNSW_Leontief_Supplement_Setting

namespace TradingPostNSW.Leontief.Supplement

theorem theorem_4_10 {n m : ℕ} (I : Instance n m) (hI : GenStanding I)
    (U : Fin n → (Fin m → ℝ) → ℝ) (hU : ∀ i, IsConcaveUtility (U i))
    (hpc : PerfectCompetitionU U) (b : Fin n → Fin m → ℝ) (hb : IsPNEU I U 0 b)
    (y : Fin n → Fin m → ℝ) (hy : Feasible I y) :
    NSWU I U y ≤ 2 * NSWU I U (tpAlloc 0 b) := by sorry

end TradingPostNSW.Leontief.Supplement
