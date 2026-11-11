-- Prove2me | Theorems.Thm_SparsestCutOracle_Main_zero_weights_reduction
-- name    : SparsestCutOracle.Main.zero_weights_reduction
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T03:37:52.061377+00:00
-- url     : https://prove2.me/theorems/8eca55df-75e3-47b1-b09f-b754f36d3866
-- title:
--   Claim 5 — Reduction from zero weights to positive weights
-- statement:
--   Suppose a family of charged programs satisfies every guarantee of Theorem 1 when all vertex weights are strictly positive, under the same normalization and polynomial total-weight domain. Then a family also satisfies the complete theorem for nonnegative weights:
--
--   $$\operatorname{BalancedOracle}(\pi>0)\quad\Longrightarrow\quad\operatorname{BalancedOracle}(\pi\ge0).$$
--
--   The approximation and balance constants may change, but the expansion threshold, probability quantifiers, admissible parameter shape, polynomial-weight quantifier and expected-work shape are preserved. The statement does not silently assume that an arbitrarily perturbed weighting already lies in the positive-only domain.
--
--   Differences from the source:
--   - reading: a randomized algorithm, with no machine specified → one finite admissible charged real-RAM program with square roots and independent standard Gaussian and fair-coin tapes; reason: the base machine is the published ClusterDecomp machine; the only new scalar instructions are square root and Gaussian sampling
--   - encoding: same asymptotic guarantees → an implication between the complete positive-only and nonnegative machine-level specifications; reason: each side quantifies its own universal constants, as the proof changes the cut factor by two and the balance factor by one half
-- source:
--   Robin Münk, Monika Henzinger, Harald Räcke, STOC 2027 submission #1170 (October 2026), p. 39, Claim 5; proof pp. 39–40

import Mathlib
import Definitions.Def_SparsestCutOracle_Main_Guarantees

namespace SparsestCutOracle.Main

/-- Claim 5, p.39: constants may change, but none of the asymptotic shapes does. -/
theorem zero_weights_reduction : BalancedOracle true → BalancedOracle false := by sorry

end SparsestCutOracle.Main
