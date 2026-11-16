-- Prove2me | Theorems.Thm_SingleCopyMoments_Adaptive_Supplement_distributed_alternating_estimation
-- name    : SingleCopyMoments.Adaptive.Supplement.distributed_alternating_estimation
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T18:43:44.858865+00:00
-- url     : https://prove2.me/theorems/f187e062-f03a-4e2d-83b2-01242a39befc
-- title:
--   Theorem 29 — Distributed alternating-moment upper bound
-- statement:
--   Fix $t\ge2$ and $\epsilon,\delta\in(0,1)$. There are $C>0$ and $d_0$, depending only on $t,\epsilon,\delta$, such that for every $d\ge\max(1,d_0)$ Alice and Bob have one protocol working for all unknown $d$-dimensional states $\rho,\sigma$ and satisfying
--   $$n_A+n_B\le C\sqrt d,\qquad
--   \Pr\{|\widehat z-\operatorname{Tr}[(\rho\sigma)^t]|\le\epsilon\}\ge1-\delta.$$
--   Alice receives $n_A$ copies and Bob receives $n_B$ copies. Arbitrary joint local operations and local quantum memory are allowed. An input-independent shared classical seed and one-way classical communication from Alice to Bob suffice. There is no quantum communication or preshared entanglement. The deterministic total budget includes unsuccessful filters, pilot and normalization trials. All local Born kernels and the joint transcript law are normalized, and the success event is measurable.
--
--   This companion theorem gives a distributed upper bound and does not add the lower bound of Corollary 3.
--
--   Differences from the source:
--   - encoding: O or Theta asymptotic copy counts → positive constants and dimension thresholds preceding unknown inputs; reason: Section 5 fixes exactly this quantifier convention; constants have only the stated permitted dependence
--   - encoding: probability of a successful estimate → normalized Born transcript law and measurable additive-success event; reason: makes the operational probability explicit without assuming successful estimation
--   - encoding: a real trace target → the real part of that trace; reason: the specified Hermitian or alternating-product target has zero imaginary part on every source instance
--   - encoding: arbitrary local joint operations with one-way classical communication → seeded Alice and message-selected Bob block POVMs on fixed tensor-power allocations; reason: every local instrument with a final classical record induces such a POVM; local quantum memory is retained within a block, and unused copies can be ignored
-- source:
--   Zhenhuan Liu, STOC 2027 submission #41 (October 2026), Theorem 29, printed p. 30 (PDF p. 32); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/41.pdf

import Definitions.Def_SingleCopyMoments_Adaptive_Supplement_Distributed

open MeasureTheory ProbabilityTheory Matrix
open scoped ENNReal ComplexOrder Topology Matrix.Norms.L2Operator
set_option autoImplicit false
noncomputable section

namespace SingleCopyMoments.Adaptive.Supplement

/-- Theorem 29, printed p.30 / PDF p.32. All allocated copies are counted. -/
theorem distributed_alternating_estimation (t : ℕ) (ht : 2 ≤ t)
    (ε δ : ℝ) (hε : ε ∈ Set.Ioo (0 : ℝ) 1) (hδ : δ ∈ Set.Ioo (0 : ℝ) 1) :
    ∃ C > (0 : ℝ), ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d → 0 < d →
    ∃ nA nB : ℕ, ∃ P : OneWayProtocol d nA nB,
      ((nA+nB : ℕ) : ℝ) ≤ C * Real.sqrt (d : ℝ) ∧
      DistributedSucceeds P t ε δ := by sorry

end SingleCopyMoments.Adaptive.Supplement
