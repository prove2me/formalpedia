-- Prove2me | Theorems.Thm_PLCMarkets_ExactCover_Supplement_theorem_5_1_rational_equilibrium_polyBits
-- name    : PLCMarkets.ExactCover.Supplement.theorem_5_1_rational_equilibrium_polyBits
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T10:19:13.527285+00:00
-- url     : https://prove2.me/theorems/fd957a4d-3263-42fd-b050-4d61871b65bc
-- title:
--   THEOREM 5.1 — an Arrow–Debreu market with an equilibrium has rational equilibrium prices of polynomial bit size
-- statement:
--   Let $M$ be an Arrow–Debreu market with finitely many agents and goods, rational nonnegative endowments $w_{ij}$ with every total supply $\sum_iw_{ij}$ positive, and additively separable, nonnegative, nondecreasing, concave, piecewise-linear utilities with rational slopes and segment lengths. Write $|M|$ for the length of the binary code of $M$ and $\operatorname{bits}(q)$ for the number of bits of the reduced numerator and denominator of a rational $q$.
--
--   There is one polynomial $P$, fixed before the market, such that for every such market $M$: if $M$ has a price equilibrium, then it has a price equilibrium $q=(q_1,\dots,q_g)$ with rational entries and
--   $$\sum_{j=1}^{g}\operatorname{bits}(q_j)\le P(|M|).$$
--
--   Here a price equilibrium is a price vector in the unit simplex at which some allocation of budget-optimal bundles clears every good exactly (§6, p. 10:10). The theorem extends the rationality of Fisher equilibria (Theorem 4.1) to exchange markets, and it gives the polynomial-size certificates used for NP membership in Theorem 8.1.
--
--   **Formalization Note** Agents and goods are `Fin a` and `Fin g`; the market is the published `ADMarket` and the equilibrium is the `SourceEquilibrium` notion. The bit size is the published `PLCMarkets.Rationality.bitSize`.
--
--   Differences from the source:
--   - generalization: each good totals 1 unit, without loss of generality (§5, p. 10:9) → any market whose goods all have positive total supply; reason: a unit-supply market is a special case, so the statement specializes to the source's
--   - encoding: prices that can be written using polynomially many bits → one polynomial P chosen before every market, bounding the total bit size of the rational prices by P(length of the market's binary code); reason: the uniform reading of 'polynomially many bits'; ∀ market ∃ polynomial would be vacuous
--   - encoding: an equilibrium (prices defined up to scaling, §5 sets M = 1) → price equilibrium in the unit simplex as defined in §6, p. 10:10; reason: every equilibrium rescales into the simplex, as §5 states
-- source:
--   Vazirani and Yannakakis, Market Equilibrium under Separable, Piecewise-Linear, Concave Utilities, J. ACM 58(3), Article 10, 2011, p. 10:9, THEOREM 5.1 (with §5 and §6, p. 10:10, for the equilibrium notion)

import Mathlib
import Definitions.Def_PLCMarkets_Rationality_EncodingSize
import Definitions.Def_PLCMarkets_ExactCover_Supplement_SourceEquilibrium
import Definitions.Def_PLCMarkets_ExactCover_Supplement_Encoding

namespace PLCMarkets.ExactCover.Supplement

open PLCMarkets.ExactCover

theorem theorem_5_1_rational_equilibrium_polyBits :
    ∃ P : Polynomial ℕ, ∀ (a g : ℕ) (M : ADMarket (Fin a) (Fin g)),
      (∀ j, 0 < M.supply j) →
      (∃ p : Fin g → ℝ, IsSrcEquilibrium M p) →
      ∃ q : Fin g → ℚ, IsSrcEquilibrium M (fun j => (q j : ℝ)) ∧
        ∑ j, PLCMarkets.Rationality.bitSize (q j) ≤ P.eval (adEncodingSize M) := by sorry

end PLCMarkets.ExactCover.Supplement
