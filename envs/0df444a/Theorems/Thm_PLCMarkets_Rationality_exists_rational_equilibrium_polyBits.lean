-- Prove2me | Theorems.Thm_PLCMarkets_Rationality_exists_rational_equilibrium_polyBits
-- name    : PLCMarkets.Rationality.exists_rational_equilibrium_polyBits
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T01:01:33.000138+00:00
-- url     : https://prove2.me/theorems/3933c21d-b17f-4e07-9562-0c50805a4eba
-- title:
--   THEOREM 4.1 — Fisher markets with an equilibrium have rational equilibrium prices of polynomial bit size
-- statement:
--   There is a polynomial $P$ with natural-number coefficients such that the following holds. Let $M$ be any Fisher market with $n$ buyers and $g$ goods, additively separable piecewise-linear concave utilities and all parameters rational (see `FisherMarket`), and let $\|M\|$ be its encoding size (see `EncodingSize`). If $M$ has an equilibrium (at real prices), then it has equilibrium prices $q=(q_1,\dots,q_g)$ that are rational numbers with
--   $$\sum_{j=1}^{g}\operatorname{bits}(q_j)\le P(\|M\|).$$
--
--   In words: every Fisher market with additively separable piecewise-linear, concave utilities and all parameters rational that has an equilibrium admits equilibrium prices that are rational numbers that can be written using polynomially many bits. This is the rationality half of the paper; it puts the existence question for such markets in NP.
--
--   **Formalization Note.** The polynomial is chosen before the market, so the bound is uniform. The hypothesis is the existence of an equilibrium at real prices; nothing else is assumed about the market beyond the model (in particular not the paper's sufficient condition for existence on p. 10:7). Bounding the total bit size of $q$ is equivalent to bounding each $\operatorname{bits}(q_j)$, since $g\le\|M\|$.
-- source:
--   Vazirani and Yannakakis, Market Equilibrium under Separable, Piecewise-Linear, Concave Utilities, J. ACM 58(3), Article 10, 2011, https://doi.org/10.1145/1970392.1970394, p. 10:9, THEOREM 4.1

import Mathlib
import Definitions.Def_PLCMarkets_Rationality_EncodingSize

namespace PLCMarkets.Rationality

/-- **THEOREM 4.1** (Vazirani–Yannakakis 2011, §4, p. 10:9). Every Fisher market with additively
separable piecewise-linear, concave utilities and all parameters rational that has an equilibrium
admits equilibrium prices that are rational numbers that can be written using polynomially many
bits: there is one polynomial `P` such that for every such market `M` with an equilibrium, some
rational equilibrium price vector has total bit size at most `P(encoding size of M)`. -/
theorem exists_rational_equilibrium_polyBits :
    ∃ P : Polynomial ℕ, ∀ (n g : ℕ) (M : FisherMarket n g),
      (∃ p : Fin g → ℝ, M.IsEquilibrium p) →
      ∃ q : Fin g → ℚ, M.IsEquilibrium (fun j => (q j : ℝ)) ∧
        ∑ j, bitSize (q j) ≤ P.eval M.encodingSize := by sorry

end PLCMarkets.Rationality
