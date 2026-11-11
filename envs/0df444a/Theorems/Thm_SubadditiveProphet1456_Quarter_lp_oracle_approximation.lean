-- Prove2me | Theorems.Thm_SubadditiveProphet1456_Quarter_lp_oracle_approximation
-- name    : SubadditiveProphet1456.Quarter.lp_oracle_approximation
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:04:54.577428+00:00
-- url     : https://prove2.me/theorems/f17fea55-4d04-43ea-854a-a62e130212ff
-- title:
--   Fact 2.1 — LP benchmark and polynomial-support demand-oracle approximation
-- statement:
--   For every independent finite-support allocation instance and every real $0\le\theta\le1$,
--   $$
--   \mathrm{LP}(\theta)^*\ge\theta\,\mathbb E[\mathrm{OPT}].
--   $$
--   Here the hindsight optimum ranges over disjoint allocations for each realized type profile. Moreover, in the rational-input specialization, one fixed demand-only rational program, given $0<\eta<1$, outputs a sparse feasible solution $x$ satisfying
--   $$
--   \sum_{i,\tau,A\ne\varnothing}x_{i,\tau,A}v_{i,\tau}(A)\ge(1-\eta)\mathrm{LP}(\theta)^*.
--   $$
--   The program halts within a fixed polynomial bound in the explicit numerical input size and $\log(1/\eta)$ on every execution; its accumulated bit/oracle work and sparse output length obey that same bound. The constants and degree precede all instances, accuracies and correct maximizing tie choices. Neither a free LP solver nor enumeration of all bundles is supplied as an input.
--
--   This is both clauses of the fact: the benchmark comparison and polynomial-support demand-oracle preprocessing. It is the computational prerequisite for the main online guarantee.
--
--   Differences from the source:
--   - encoding: Finite items and nonempty finite buyer type supports in fixed arrival order → Zero-based Fin indices and type supports Fin (k+1), with positive type probabilities; reason: Relabeling covers every source instance, including empty item or buyer sets; zero-probability labels are omitted from support
--   - encoding: Polynomial time and polynomial support in the rational-input demand-oracle model → One finite demand-only bit program and fixed constants C,d chosen before all inputs, with bounded-time execution and a sparse decoded LP output; reason: Operational semantics make preprocessing and output explicit; maximum numerical bit length does not assume an exponential valuation table is available
--   - encoding: The standard rational-input oracle model, with numerical encoding lengths included in the input size → A public upper bound on the bit length of every rational valuation value is supplied to the demand-only program and charged in its input size; reason: Every finite rational support admits this bound, and any larger bound is allowed; exposing numerical size metadata makes bundle-only demand access usable without supplying a valuation table or an LP solver
-- source:
--   Twan Kroll, Calum MacRury, Rebecca Reiffenhäuser, Siddharth M. Sundaram, STOC 2027 submission #1456 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1456.pdf, printed p.8, PDF p.9, Fact 2.1.

import Definitions.Def_SubadditiveProphet1456_Quarter_CapHeight
import Definitions.Def_SubadditiveProphet1456_Quarter_Machine

open scoped BigOperators NNReal ENNReal
open MeasureTheory

namespace SubadditiveProphet1456.Quarter

theorem lp_oracle_approximation :
    (∀ (n m : ℕ) (I : Instance n m) (θ : ℝ), 0 ≤ θ → θ ≤ 1 →
      θ*expectedOffline I ≤ lpValue I θ) ∧
    ∃ (program : BitProgram) (C : ℝ) (d : ℕ), 0 < C ∧
    ∀ (n m : ℕ) (I : Instance n m) (R : RationalData I) (θ η : ℚ),
      0 ≤ θ → θ ≤ 1 → 0 < η → η < 1 →
      ∀ O : DemandOracle I, CorrectDemand I O →
      let B := ⌈polyBound C d (inputSize R [θ,η]) (Real.log (1/(η:ℝ)))⌉₊
      ∃ T : ℕ, T ≤ B ∧ ∀ z : BitState Unit,
        bitRun program (preprocessingPort R O) (preprocessingInit R θ η) T z ≠ 0 →
        z.halted = true ∧ z.work ≤ B ∧
          ApproximateLPOutput I (θ:ℝ) (η:ℝ) B z.left := by sorry

end SubadditiveProphet1456.Quarter
