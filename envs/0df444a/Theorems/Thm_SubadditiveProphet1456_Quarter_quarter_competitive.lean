-- Prove2me | Theorems.Thm_SubadditiveProphet1456_Quarter_quarter_competitive
-- name    : SubadditiveProphet1456.Quarter.quarter_competitive
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:04:50.044041+00:00
-- url     : https://prove2.me/theorems/a2d13e70-9263-4347-a681-c5ada4bc21f6
-- title:
--   Theorem 1.1 — Main result: welfare and expected polynomial time
-- statement:
--   Let independent buyers with arbitrary finite-support normalized, monotone, nonnegative subadditive valuations arrive in their given fixed order. For every real $\varepsilon>0$ there is a causal randomized allocation policy $P$, supported on pairwise disjoint allocations, satisfying
--   $$
--   \mathbb E[\textstyle\sum_i v_i(P_i)]\ge(1/4-\varepsilon)\mathrm{LP}(1)^*.
--   $$
--   Here $\mathrm{LP}(1)^*$ is the concrete ex-ante configuration-LP optimum, rather than the expected hindsight optimum.
--
--   Moreover, one fixed rational instruction program implements such a policy for every rationally encoded instance and positive rational accuracy, for every correct support demand oracle. Its output law is the same policy law used in the welfare inequality, and its expected total bit/oracle cost is at most $C(1+L+1/\varepsilon)^d$, with $C>0$ and natural $d$ fixed before every instance. The size $L$ includes $n,m$, total support size, numerical bit lengths and the accuracy encoding. Preprocessing, random sampling and irrevocable online outputs are all charged. The real mathematical clause has no rationality or bounded-range restriction.
--
--   This is the full main welfare and implementation result; it supplies an ex-ante competitive causal algorithm, including the nonpositive-target regime $\varepsilon\ge1/4$.
--
--   Differences from the source:
--   - encoding: Finite items and nonempty finite buyer type supports in fixed arrival order → Zero-based Fin indices and type supports Fin (k+1), with positive type probabilities; reason: Relabeling covers every source instance, including empty item or buyer sets; zero-probability labels are omitted from support
--   - encoding: Arbitrary real finite-support valuations mathematically and the standing rational-input demand-oracle model for running time → Unrestricted real policy existence together with a uniform rational program whose own allocation law has the welfare guarantee and expected bit bound; reason: The computational specialization does not restrict the mathematical welfare domain; the same executed law is used for welfare and runtime in that specialization, with all numerical sizes charged
--   - encoding: The standard rational-input oracle model, with numerical encoding lengths included in the input size → A public upper bound on the bit length of every rational valuation value is supplied to the demand-only program and charged in its input size; reason: Every finite rational support admits this bound, and any larger bound is allowed; exposing numerical size metadata makes bundle-only demand access usable without supplying a valuation table or an LP solver
-- source:
--   Twan Kroll, Calum MacRury, Rebecca Reiffenhäuser, Siddharth M. Sundaram, STOC 2027 submission #1456 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1456.pdf, printed p.1, PDF p.2, Theorem 1.1.

import Definitions.Def_SubadditiveProphet1456_Quarter_CapHeight
import Definitions.Def_SubadditiveProphet1456_Quarter_Machine

open scoped BigOperators NNReal ENNReal
open MeasureTheory

namespace SubadditiveProphet1456.Quarter

theorem quarter_competitive :
    (∀ (n m : ℕ) (I : Instance n m) (ε : ℝ), 0 < ε →
      ∃ P : Policy I, IsOnline I P ∧ (1/4-ε)*lpValue I 1 ≤ policyWelfare I P) ∧
    ∃ (program : BitProgram) (C : ℝ) (d : ℕ), 0 < C ∧
      ∀ (n m : ℕ) (I : Instance n m) (R : RationalData I) (ε : ℚ), 0 < ε →
        ∀ O : DemandOracle I, CorrectDemand I O →
          ∃ P : Policy I, IsOnline I P ∧
            (1/4-(ε:ℝ))*lpValue I 1 ≤ policyWelfare I P ∧
            ImplementsOnline program R ε O P ∧
            onlineCost program R ε O ≤
              ENNReal.ofReal (polyBound C d (inputSize R [ε]) (1/(ε:ℝ))) := by sorry

end SubadditiveProphet1456.Quarter
