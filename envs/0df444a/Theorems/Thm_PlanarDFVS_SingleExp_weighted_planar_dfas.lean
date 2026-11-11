-- Prove2me | Theorems.Thm_PlanarDFVS_SingleExp_weighted_planar_dfas
-- name    : PlanarDFVS.SingleExp.weighted_planar_dfas
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:08:39.981595+00:00
-- url     : https://prove2.me/theorems/59f28dc6-d0ce-47f7-8d65-999ce5136e56
-- title:
--   Theorem 3.5 — polynomial weighted planar feedback arc set
-- statement:
--   For every planar directed multigraph with arbitrary finite arc costs, there is a uniform polynomial-time algorithm returning a minimum-cost feedback arc set. Both signs of finite costs are allowed. Arcs may also be forbidden; the algorithm reports infeasibility exactly when no feedback arc set avoids the forbidden arcs.
--
--   $$\min\Bigl\{\sum_{a\in A}c(a):D-A\text{ acyclic},\ A\cap F=\varnothing\Bigr\}.$$
--
--   The real-cost statement uses exact arithmetic and comparisons; the rational-cost statement uses binary encodings and bit work polynomial also in the weight encoding length. The programs, positive coefficients and fixed degrees precede all graph and weight inputs. Their full arc-list input accounts for multiplicities. This is a weighted optimizer, including the unit-cost and forbidden-arc application, with actual charged computations.
--
--   Differences from the source:
--   - reading: weighted input representation and elementary cost model unspecified; proof of Lemma 3.6 uses infinite prohibitive weights → arbitrary finite real weights in arithmetic/comparison cost, rational weights in bit cost, separate forbidden-arc flags and an infeasible result; reason: retains the complete weighted optimization and its application; negative costs cover either sign convention, and legal sums never perform infinity arithmetic
--   - encoding: polynomial running time in weighted graph input → fixed positive coefficients and natural exponents before all inputs, measured on the full encoded arc and weight data; reason: an unbounded explicit duplicate list is charged by its encoded length rather than by the number of vertices alone
--   - generalization: loopless digraphs under the standing convention following Observation 2.1 → all planar digraphs, including loops; reason: restricting to loopless inputs recovers the source; every loop arc is forced into a feedback arc set, and a forbidden loop makes the instance infeasible
-- source:
--   Daniel Lokshtanov, Saket Saurabh, Jie Xue, STOC 2027 submission #1569 (October 2026), p. 7 (PDF p. 7), Theorem 3.5 (Theorems 4.10 and 4.12 of [MSW22])

import Mathlib
import Definitions.Def_PlanarDFVS_SingleExp_Interfaces

open scoped BigOperators
open Classical

namespace PlanarDFVS.SingleExp

theorem weighted_planar_dfas :
    ∃ (R B : Program) (CR CB : ℝ) (dR dB : ℕ),
      0 < CR ∧ 0 < CB ∧
      RealWeightedGuarantee R CR dR ∧ RationalWeightedGuarantee B CB dB := by sorry

end PlanarDFVS.SingleExp
