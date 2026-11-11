-- Prove2me | Theorems.Thm_SubadditiveProphet1456_Quarter_buyer_wise_retention
-- name    : SubadditiveProphet1456.Quarter.buyer_wise_retention
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:04:49.820574+00:00
-- url     : https://prove2.me/theorems/32d63e97-0fd1-4e46-8b4b-2e0e11b501d5
-- title:
--   Lemma 4.3 — Conditional buyer-wise retention with efficient scoring
-- statement:
--   Fix $0<\theta<1$, a feasible configuration-LP solution $x$, and $0<\delta<1/4$. Write $c$ for the explicit positive universal constant from Appendix A. Set
--   $$
--   N=1+\left\lceil\frac{\log\max\{1,m\theta^2/[\delta(1-\theta)^2]\}}{2\log(1+c)}\right\rceil.
--   $$
--   The CapHeight generators satisfy the capped distributional equation. The fresh-internal-profile implementation has exactly their type-conditional score laws. For every buyer $i$, type $\tau$, and bundle $A$ of positive conditional tentative probability,
--   $$
--   \mathbb E[v_i(\mathrm{ALG}_i)\mid \tau_i=\tau,X_i=A]\ge(1/4-\delta)v_{i,\tau}(A).
--   $$
--   Each call of that implementation has expected work at most $C(1+n+m+1/\delta+1/(1-\theta))^d$, for fixed $C,d$, relative to tentative sampling access. The conclusion retains the conditioning on both type and bundle. It also asserts positivity of the integral constant used to choose the cap.
--
--   This conditional interface is what permits summing buyer welfare and accounting for approximate LP preprocessing without postulating an exact LP oracle.
--
--   Differences from the source:
--   - encoding: Finite items and nonempty finite buyer type supports in fixed arrival order → Zero-based Fin indices and type supports Fin (k+1), with positive type probabilities; reason: Relabeling covers every source instance, including empty item or buyer sets; zero-probability labels are omitted from support
--   - generalization: An optimal LP(theta) solution with its induced tentative distributions → Every feasible LP(theta) solution, with the same induced distributions and unit sampling access; reason: The recursion, subcriticality and retention arguments use feasibility only; specializing to an optimal solution recovers every printed instance and permits charged approximate preprocessing
--   - encoding: Expected polynomial scoring time given tentative-bundle sampling access → Expected accumulated work of the recursive sampler with explicit local integer/coordinate charges; reason: Local charges cover the stated sampling and threshold operations with fixed polynomial overhead; the goal separately pays for preprocessing and bit-level sampling
--   - encoding: There exists a positive universal c, with an explicit witness in the proof of Lemma A.3 → The explicit integral witness tailConstant, with positivity asserted and no instance parameters; reason: This selects the paper proof's own constant uniformly before all instances
--   - encoding: There is a choice of cap N → The exact cap expression supplied on printed p.14/PDF p.15; reason: The source proof establishes this explicit choice for every allowed accuracy and instance
-- source:
--   Twan Kroll, Calum MacRury, Rebecca Reiffenhäuser, Siddharth M. Sundaram, STOC 2027 submission #1456 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1456.pdf, printed p.12, PDF p.13, Lemma 4.3.

import Definitions.Def_SubadditiveProphet1456_Quarter_CapHeight
import Definitions.Def_SubadditiveProphet1456_Quarter_Machine

open scoped BigOperators NNReal ENNReal
open MeasureTheory

namespace SubadditiveProphet1456.Quarter

theorem buyer_wise_retention :
    0 < tailConstant ∧ ∃ (C : ℝ) (d : ℕ), 0 < C ∧
    ∀ (n m : ℕ) (I : Instance n m) (θ δ : ℝ) (x : Fractional I),
      0 < θ → θ < 1 → Feasible I θ x → 0 < δ → δ < 1/4 →
      let N := retentionCap tailConstant δ θ m
      DistributionalEquation I x N (capRSG I x N) ∧
      retentionRSG I x N = capRSG I x N ∧
      (∀ (i : Fin n) (t : Fin (I.types i+1)) (A : Bundle m),
        0 < tentativeMass I x i t A →
          (1/4-δ)*I.valuation i t A ≤ conditionalRetention I x N i t A) ∧
      (∀ (i : Fin n) (t : Fin (I.types i+1)),
        retentionExpectedCost I x N i t ≤ ENNReal.ofReal
          (polyBound C d (n+m) (1/δ+1/(1-θ)))) := by sorry

end SubadditiveProphet1456.Quarter
