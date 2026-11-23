-- Prove2me | Theorems.Thm_UniformPrecSched_Makespan_Supplement_theorem_4_1
-- name    : UniformPrecSched.Makespan.Supplement.theorem_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T07:25:50.812568+00:00
-- url     : https://prove2.me/theorems/076a67c1-ef4e-4ff6-883b-97c72fbcee89
-- title:
--   Theorem 4.1 — polynomial-time weighted completion approximation with releases
-- statement:
--   There exist a positive absolute constant $c$, a single finite tape machine and fixed polynomial time bound that implement the interval-LP/filter/list-scheduling/concatenation construction on binary rational input. The same pipeline has outputs for every real scheduling instance with positive processing requirements and speeds, strict precedence, nonnegative release dates $r_j$ and nonnegative weights $w_j$.
--
--   Every permitted output is a feasible nonpreemptive schedule respecting all releases and, for every feasible release-date schedule $\sigma^*$ of the original instance, satisfies
--
--   $$\sum_j w_j C_j(\sigma)\le16\rho_c(I)\sum_j w_j C_j(\sigma^*),$$
--
--   where $K$ is the original number of distinct speeds and
--
--   $$\rho_c(I)=\begin{cases}\min\{K+2\sqrt K+1,\;1.89\log_2m+c\sqrt{\log_2m}\},&m\ge2,\\ K+2\sqrt K+1,&m=1.\end{cases}$$
--
--   The machine takes at most $a(B+1)^d$ ordinary tape steps on each valid rational input of encoded length $B$, for fixed natural constants $a>0,d$. LP solving is included in this cost. This states an efficient approximation by the specified algorithm, rather than existence of a good schedule. The factor 16 and both branches are retained.
--
--   **Formalization Note** The approximation property in the conclusion expands to polynomial implementation, real-input output existence, and correctness of every permitted pipeline output. No performance or runtime inequality is assumed by a run. The finite input encoding is rational in binary; the mathematical correctness statement does not restrict real data.
--
--   Differences from the source:
--   - encoding: uniform-speed schedules with release dates and weighted completion cost → the immutable finite real model with nonnegative releases and weights, including zeros; reason: makes the standing scheduling convention explicit without ordering releases by precedence
--   - encoding: O(√log m) → a single positive c chosen before every input; reason: the remainder constant must be absolute, and the factor 16 multiplies the entire minimum
--   - reading: the logarithmic asymptotic guarantee written as a minimum → the minimum for m≥2 and the finite-K branch for m=1; reason: at m=1 log₂m=0 would make the literal second branch zero; the paper’s construction supplies the finite-K branch there
--   - encoding: without-loss time scaling p_j/s_k≥1 and a logarithmic horizon → explicit reversible scaling, ceiling horizon, first level [1,2], and zero-mass extension through all assigned levels; reason: covers arbitrary positive durations and zero-weight LP optima whose completion variables can exceed the original horizon
--   - encoding: general speed rounding with α≥1 and β>1, illustrated by α=log₂m and β=e → α=max(1,ceil(log₂m)) and β=68/25; reason: these permitted rational-preserving choices retain coefficient 1.89 with an absolute remainder; c=64 is supported by the brief’s estimates
--   - encoding: shifted fragments using a common guaranteed ratio ρ → ρ=max(1,max_l makespan(F_l)/2^(l+1)) in the same shifted-window formula; reason: each fragment fits by construction and this measured ratio is at most the theoretical minimum bound; rational inputs have rational output starts
--   - reading: polynomial-time algorithm on finitely encoded scheduling data → one finite Mathlib tape machine, polynomial in explicit binary rational input length, implementing the pipeline whose real-input correctness is unrestricted; reason: gives operational bit complexity and charges LP solving and encoded magnitudes without claiming a finite bit encoding of arbitrary reals
--   - generalization: the constructed algorithm’s approximation guarantee → correctness for every permitted LP optimum, assignment tie and speed-list output, together with one fixed polynomial-time implementation; reason: the source estimates use only the retained LP and nonidle-list properties; in particular they apply to the algorithm selected by that implementation
--   - generalization: a finite list of jobs → also the empty job set with zero cost; reason: the empty output satisfies feasibility and the same bound, so no nonempty source instance is lost
-- source:
--   Chudak & Shmoys, Approximation algorithms for precedence-constrained scheduling problems on parallel machines that run at different speeds, authors' manuscript (preprint of J. Algorithms, 1999, DOI 10.1006/jagm.1998.0987), p. 14 (PDF 14), Theorem 4.1; pp. 12–14 (PDF 12–14), construction

import Mathlib
import Definitions.Def_UniformPrecSched_Makespan_Supplement_BitImplementation

namespace UniformPrecSched.Makespan.Supplement

/-- Chudak–Shmoys, authors' manuscript, p. 14, PDF 14, Theorem 4.1;
construction pp. 12–14. A uniform polynomial-time implementation of the actual
interval-LP algorithm, with unrestricted real-input correctness for its output
specification, including the empty job set and zero weights.
Formalization Note: comparison is against every feasible original-instance schedule.
The m=1 case uses the finite-K branch. Polynomial time is charged in binary tape steps
on rational input; the real specification uses the same LP and arithmetic operations. -/
theorem theorem_4_1 :
    ∃ (c : ℝ) (q a d : ℕ) (A : SchedulingMachine q),
      0 < c ∧ 0 < a ∧ IsApproximationAlgorithm c A a d := by sorry

end UniformPrecSched.Makespan.Supplement
