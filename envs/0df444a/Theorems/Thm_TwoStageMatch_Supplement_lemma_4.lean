-- Prove2me | Theorems.Thm_TwoStageMatch_Supplement_lemma_4
-- name    : TwoStageMatch.Supplement.lemma_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-26T22:13:34.159576+00:00
-- url     : https://prove2.me/theorems/d2b5cfd0-9357-5930-a734-29fa24249089
-- title:
--   Lemma 4: the optimal value of $\mathcal P^{\mathrm{EAR}}$ is at least $\mathrm{OPT}_{\text{offline-MP}}$ (corrected: atomless value laws with finite mean)
-- statement:
--   Consider a two-stage joint matching and pricing instance: a bipartite graph between demands $D_1\cup D_2$ and supplies $S$, supply weights $w_j\ge0$, contributions $\hat w_i=w_i(p_i)\ge0$ of first-stage demands, and independent values $v_i\sim F_i$ on $[0,\infty)$ of second-stage demands, each $F_i$ atomless with finite mean. Then some fractional matching $x$ of $G$ has
--   $$\sum_{i\in D_1}\hat w_iy_i+\sum_{i\in D_2}w_i(T_i(y_i))\,y_i+\sum_{j\in S}w_jy_j\ \ge\ \mathrm{OPT}_{\text{offline-MP}},$$
--   where $y_i=\sum_jx_{ij}$, $y_j=\sum_ix_{ij}$, $w_i(p)=\mathbb E[v_i\mid v_i\ge p]$ and $T_i(q)=\max\{t:1-F_i(t)\ge q\}$. Hence the optimal value of the ex ante relaxation $\mathcal P^{\mathrm{EAR}}$ is at least $\mathrm{OPT}_{\text{offline-MP}}$.
--
--   This is the upper bound on the benchmark against which Algorithm 3 is analyzed (Theorem 4).
--
--   Differences from the source:
--   - correction: Lemma 4, Theorem 4 and Theorem EC.4 are stated for arbitrary value laws F_i, with T_i(q) ≜ argmax{t : 1 − F_i(t) ≥ q} and the claim that i accepts the price T_i(y_i) with probability y_i (p.27) → every second-stage law F_i is atomless with finite mean (MPInstance.Regular); reason: for a law with an atom the argmax does not exist and no price is accepted with probability y_i: for a point mass at 1 and any q ∈ (0,1), {t : 1 − F(t) ≥ q} = (−∞, 1) has no maximum and every price is accepted with probability 0 or 1; a finite mean is needed for w_i(p) = E[v | v ≥ p] to be a real number. Excluded: laws with atoms and laws with infinite mean
--   - reading: values v_i ∼ F_i of demands for the service (p.8), never given a sign → each F_i is carried by [0, ∞); reason: a value for the service is a non-negative willingness to pay; the paper's welfare objective, its examples (uniform values, the two-point law on {0, 1/ε}) and its formula w_i(T_i(y))y = ∫_0^y T_i(q)dq all use non-negative values
--   - encoding: first-stage demands carry a law F_i and an accepted price p_i, contributing w_i(p_i) → each first-stage demand carries ŵ_i = w_i(p_i) ≥ 0 directly; reason: only w_i(p_i) enters the problem, and every ŵ_i ≥ 0 is w_i(p_i) for some law and price (a point mass at ŵ_i), so the instances are the same
--   - encoding: the optimal value of 𝒫^EAR is at least OPT_offline-MP → some feasible point of 𝒫^EAR has objective at least OPT_offline-MP; reason: the supremum of the objective is at least OPT_offline-MP iff such points exist, the optimum being attained (the proof constructs the point)
-- source:
--   Feng, Niazadeh & Saberi, Two-stage Stochastic Matching and Pricing with Applications to Ride Hailing, arXiv:2210.11648v1, Lemma 4, p.25

import Mathlib
import Definitions.Def_TwoStageMatch_Supplement_Algorithm3

namespace TwoStageMatch.Supplement

/-- **Lemma 4** (Feng, Niazadeh & Saberi, arXiv:2210.11648v1, p.25). The optimal value of program
`𝒫^EAR` is at least `OPT_offline-MP`.

Stated on every joint matching/pricing instance whose second-stage value laws are atomless with
finite mean: some feasible point of `𝒫^EAR` (a fractional matching of `G`) has objective at least
`OPT_offline-MP`.

**Formalization Note.** "The optimal value is at least `OPT_offline-MP`" is stated as the
existence of a feasible point with objective at least `OPT_offline-MP` (the supremum is then at
least `OPT_offline-MP`; the proof constructs such a point). The threshold `T_i` of `𝒫^EAR` needs
atomless laws (see the correction in the natural-language statement). -/
theorem lemma_4 {D₁ D₂ S : Type*} [Fintype D₁] [Fintype D₂] [Fintype S] (I : MPInstance D₁ D₂ S)
    (hI : I.Regular) :
    ∃ x, IsFracMatching I.E Finset.univ Finset.univ x ∧ optOfflineMP I ≤ earObjective I x := by sorry

end TwoStageMatch.Supplement
