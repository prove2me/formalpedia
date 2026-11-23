-- Prove2me | Theorems.Thm_RossQC_Regions_Supplement_theorem_2_2_prime
-- name    : RossQC.Regions.Supplement.theorem_2_2_prime
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T09:04:05.311693+00:00
-- url     : https://prove2.me/theorems/32bc6058-b781-4d6f-b6ad-df6f5b052518
-- title:
--   Theorem 2.2′ — the average-cost optimal inspect and revise regions are convex
-- statement:
--   Consider the general model of Ross's §2: countably many underlying states, a stochastic transition matrix $(P_{ij})$, bounded costs $C_i,I_i,R_i$, the belief simplex $S$, the update $(TP)_i=\sum_jP_jP_{ji}$ and the beliefs $e^i=(P_{i0},P_{i1},\dots)$. For $b\in(0,1)$ let $V_b$ be the discounted optimal cost, fix $P^0\in S$, and let $f_b(P)=V_b(P)-V_b(P^0)$. Suppose $\{f_b(P):P\in S,\ b\in(0,1)\}$ is uniformly bounded and equicontinuous.
--
--   Let $(f,g)$ be any pair with the properties the paper's quoted theorem (Ross, 1968) gives:
--   1. the average-cost optimality equation (2) holds on $S$:
--   $$
--   g+f(P)=\min\Big\{\sum_i P_iC_i+f(TP);\ \sum_i P_iI_i+\sum_i P_if(e^i);\ \sum_i P_iR_i+f(e^0)\Big\};
--   $$
--   2. $g=\lim_{\beta\to1^-}(1-\beta)V_\beta(P)$ for every $P\in S$;
--   3. $f(P)=\lim_{r\to\infty}f_{\beta_r}(P)$ for every $P\in S$, along some sequence $\beta_r\in(0,1)$, $\beta_r\to1$.
--
--   Then the average-cost optimal inspect region $\{P\in S: g+f(P)=\sum_iP_iI_i+\sum_iP_if(e^i)\}$ and the average-cost optimal revise region $\{P\in S: g+f(P)=\sum_iP_iR_i+f(e^0)\}$ are both convex.
--
--   This is the long-run average-cost analogue of Theorem 2.2: under the average-cost criterion, too, the beliefs at which inspecting, respectively revising, is optimal form convex sets.
--
--   **Formalization Note** The regions are subsets of $S$, defined from (2) as the $\beta$-optimal regions are defined from (1). The right side of (2) is the base right side of (1) with $\beta=1$. $V_\beta$ is the base mission's limit of value iteration. The existence of a pair $(f,g)$ is the quoted theorem's content and is not part of this statement.
--
--   Differences from the source:
--   - reading: "the average-cost optimal regions" of the pair $(f,g)$ supplied by the quoted theorem, with $f$ bounded → the regions of every pair $(f,g)$ satisfying (2) on $S$ and both limits in (b), boundedness of $f$ not restated; reason: the paper determines $(f,g)$ only through the quoted theorem; under uniform boundedness, boundedness of $f$ on $S$ follows from the limit in (b), so the pairs are the same.
--   - reading: "equicontinuous", no metric named → equicontinuity at every point of $S$ for the $\ell^1$ distance $\sum_i|P_i-Q_i|$; reason: the paper specifies no metric; this makes the topology convention explicit without assuming continuity or changing the countable state domain; both conclusions follow already from pointwise limits of concave discounted values and (2).
--   - encoding: $V_\beta$ as the infimum over policies → $V_\beta$ as the limit of value iteration from $V^0=0$ (the base mission's definition) at discount $b$; reason: inherited published convention, justified on p. 589 by "$V^n_\beta(P)\to V_\beta(P)$".
-- source:
--   Ross, Quality Control under Markovian Deterioration, Management Science 17(9):587–596 (1971), DOI 10.1287/mnsc.17.9.587, p. 590, Theorem 2.2′

import Mathlib
import Definitions.Def_RossQC_Regions_Model
import Definitions.Def_RossQC_Regions_Supplement_AverageCost

namespace RossQC.Regions.Supplement

/-- Ross, *Quality Control under Markovian Deterioration*, Management Science 17(9):587–596 (1971),
DOI 10.1287/mnsc.17.9.587, p. 590, Theorem 2.2′: "If `{f_β(P)}` is uniformly bounded and
equicontinuous then both the average-cost optimal inspect and revise regions are convex."

Under the standing hypotheses of §1–§2 (`Model.Valid`), for a reference belief `P⁰ ∈ S` such that
the relative values `f_b`, `b ∈ (0, 1)`, are uniformly bounded and equicontinuous on `S`, and for
every pair `(f, g)` with the properties (a)–(b) of the Theorem quoted on p. 589 (`IsAvgCostPair`:
`(f, g)` solves (2) on `S`, `g = lim_{β→1⁻} (1 − β)V_β(P)`, `f = lim_r f_{β_r}`), the average-cost
optimal inspect region and the average-cost optimal revise region are convex.

**Formalization Note.** The regions are subsets of `S`, defined from (2) as the base regions are
from (1) (proof of Theorem 2.2′). The statement holds for every pair the quoted Theorem can supply;
the existence of such a pair is that Theorem's content and is not asserted. Equicontinuity
uses the `ℓ¹` distance on `S`; boundedness of `f` on `S` follows from `hfam` and the
pointwise limit in `hfg`, rather than being an additional premise. -/
theorem theorem_2_2_prime {ι : Type*} [Countable ι] (M : Model ι) (hM : M.Valid)
    (P₀ : ι → ℝ) (hP₀ : P₀ ∈ M.simplex) (hfam : UnifBddEquicont M P₀)
    (f : (ι → ℝ) → ℝ) (g : ℝ) (hfg : IsAvgCostPair M P₀ f g) :
    Convex ℝ (acInspectRegion M f g) ∧ Convex ℝ (acReviseRegion M f g) := by sorry

end RossQC.Regions.Supplement
