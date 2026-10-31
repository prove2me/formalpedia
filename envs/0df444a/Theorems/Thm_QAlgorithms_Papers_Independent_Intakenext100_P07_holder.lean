-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P07_holder
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P07.holder
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T03:58:58.100709+00:00
-- url     : https://prove2.me/theorems/1c14ba1f-ac38-4098-b524-d69950011231
-- title:
--   3.3
-- statement:
--   All quantum systems below are finite-dimensional complex Hilbert spaces of positive dimension, and logarithms are binary. A normalized state is positive semidefinite with trace one; a subnormalized state has trace at most one. Marginals are partial traces. Here $F$ is squared algebraic fidelity, $F_*$ is squared generalized fidelity, $P=\sqrt{1-F_*}$ is purified distance, and $\Delta(\rho,\tau)=\max_{0\le M\le I}|\operatorname{Tr}((\rho-\tau)M)|$.
--
--   For conjugate real exponents 1/p+1/q=1, p>1: |Tr LK|≤Tr|LK|≤||L||_p||K||_q, with an attaining K for each L. For 0<p<1 and M supported by N: Tr MN≥||M||_p / ||N^{-1}||_{-q}. For positive M,N equality holds when M^p=a N^q, a≥0.
--
--   $$
--   |\operatorname{Tr}(LK)|\le\operatorname{Tr}|LK|\le\|L\|_p\|K\|_q,\qquad \operatorname{Tr}(MN)\ge\|M\|_p\|N^{-1}\|_{-q}^{-1}.
--   $$
--
--   This result records the source’s operational or structural relation, with the stated endpoint and attainment clauses retained.
-- source:
--   Quantum Information Processing with Finite Resources -- Mathematical Foundations, arXiv:1504.00233v5, PDF p. 40, 3.3

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P07

noncomputable section

open Filter

open scoped BigOperators Matrix ComplexConjugate ComplexOrder Matrix.Norms.L2Operator Topology

namespace QAlgorithms.Papers.Independent.Intakenext100.P07

attribute [local instance] Classical.propDecidable Classical.decEq

variable {I J A B C D X Y Z : Type*}

variable [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

variable [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

variable [Fintype C] [DecidableEq C] [Fintype D] [DecidableEq D]

variable [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]

variable [Fintype Z] [DecidableEq Z]

/-- NODE paper:1504.00233#3.3
3.3, arXiv:1504.00233v5, PDF p.40. -/
theorem holder [Nonempty I] (p q : ℝ) (hp : 0 < p) (hq : q ≠ 0) (hc : 1/p+1/q = 1) :
    (1 < p → ∀ L K : paperMat I, ‖(L*K).trace‖ ≤ traceNorm (L*K) ∧ traceNorm (L*K) ≤ paperSchatten L p*paperSchatten K q) ∧
    (1 < p → ∀ L : paperMat I, ∃ K : paperMat I, ‖(L*K).trace‖ = traceNorm (L*K) ∧ traceNorm (L*K) = paperSchatten L p*paperSchatten K q) ∧
    (p < 1 → ∀ M N : paperMat I, M.PosSemidef → N.PosSemidef → paperSupported M N →
      paperSchatten M p*(paperSchatten (paperPower N (-1)) (-q))⁻¹ ≤ (M*N).trace.re) ∧
    (∀ M N : paperMat I, M.PosSemidef → N.PosSemidef → (∃ a : ℝ, 0 ≤ a ∧ paperPower M p = (a:ℂ) • paperPower N q) →
      (1 < p → ‖(M*N).trace‖ = traceNorm (M*N) ∧ traceNorm (M*N) = paperSchatten M p*paperSchatten N q) ∧
      (p < 1 → paperSupported M N → (M*N).trace.re = paperSchatten M p*(paperSchatten (paperPower N (-1)) (-q))⁻¹)) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P07

end
