-- Prove2me | Theorems.Thm_PosIndexNash_PPADS_positive_payoff_shift
-- name    : PosIndexNash.PPADS.positive_payoff_shift
-- status  : Open
-- author  : @Mr Robbins
-- created : 2026-11-23T02:42:24.039813+00:00
-- url     : https://prove2.me/theorems/9cf4ba81-d837-42b1-af25-14300767490d
-- title:
--   Theorem 3.2, normalization step — polynomial-time positive-payoff shift preserves Positive-Index Nash
-- statement:
--   There is a polynomial-time search reduction
--   $$
--   \textsc{Positive-Index Nash}\;\le_p\;\textsc{Positive-Index Nash with Positive Payoffs}.
--   $$
--   On a promised nondegenerate rational game $(A,B)$, the instance map adds rational constants to the entries of $A$ and of $B$ so that both matrices become strictly positive. The shifted game remains nondegenerate, and an exact rational equilibrium of index $+1$ for the shifted game decodes to such an equilibrium for the original game.
--
--   This is the normalization at the start of §3.1. Adding a constant to every entry of one player's payoff matrix leaves best responses and Nash equilibria unchanged; the bordered-determinant identity (2) shows that it also leaves the Shapley index unchanged.
--
--   **Formalization Note** Polynomial time and correctness on promised inputs are expressed by `CardinalMatching.SearchReduces`. The target problem is `PositivePayoffNash`, whose only additional promise is entrywise positivity.
-- source:
--   Kontogiannis, Panageas, Pollatos, Yan, Finding a Positive Index Nash Equilibrium is PPADS-Complete, arXiv:2609.23879 (held PDF, sha256 00d5c5ce…cbb6), p. 12, eq. (2) and the paragraph after Definition 2.1; p. 14, first paragraph of §3.1 (positive-payoff shift for Theorem 3.2)

import Mathlib
import Definitions.Def_CardinalMatching_SearchReduces
import Definitions.Def_PosIndexNash_PPADS_PositiveIndexNash
import Definitions.Def_PosIndexNash_PPADS_PositivePayoffNash

open PosIndexNash.PPADS

theorem PosIndexNash.PPADS.positive_payoff_shift :
    CardinalMatching.SearchReduces PositiveIndexNash PositivePayoffNash := by sorry
