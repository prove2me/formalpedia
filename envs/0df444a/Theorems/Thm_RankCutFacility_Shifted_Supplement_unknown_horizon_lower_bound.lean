-- Prove2me | Theorems.Thm_RankCutFacility_Shifted_Supplement_unknown_horizon_lower_bound
-- name    : RankCutFacility.Shifted.Supplement.unknown_horizon_lower_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T18:28:17.495775+00:00
-- url     : https://prove2.me/theorems/221f9ee9-7a74-4595-a465-1608a0ae6068
-- title:
--   Theorem D.1 — Unknown-horizon deterministic lower bound $4$
-- statement:
--   A **deterministic horizon-free algorithm** maps every revealed request prefix to the candidates it opens in that round and is used unchanged whatever the number of requests. Its cost is $\sum_{y\in O_n}f_y+\sum_t d(v_t,O_t)$ with $d(x,\emptyset)=+\infty$.
--
--   **Theorem D.1.** For every $C<4$, no deterministic horizon-free algorithm is $C$-competitive on all finite random-order facility-location instances with arbitrary positive opening costs. This remains true when every request occurs at one point and when every metric point is a feasible facility. Precisely, there are a finite set $S\subset\mathbb R$ with the Euclidean distance, a point $x\in S$, a nonempty candidate set $F\subseteq S$ and positive costs on $F$ such that every deterministic horizon-free algorithm has some $n\ge1$ for which $n$ copies of $x$, in uniformly random order, satisfy
--
--   $$\mathbb E[\mathrm{ALG}]>C\cdot\mathrm{OPT};$$
--
--   and the same holds for some finite $S\subset\mathbb R$, $x\in S$ and positive costs with $F=S$.
--
--   With Corollary 4.11 this separates the known-horizon and unknown-horizon deterministic models.
--
--   Differences from the source:
--   - generalization: for every algorithm some finite instance violates C-competitiveness → one finite one-dimensional metric with one request point and fixed costs, chosen before the algorithm; only the number of requests depends on the algorithm; reason: this is the family the source's proof uses and it implies the source's statement
--   - encoding: a finite one-dimensional Euclidean metric → a Finset S of reals with the distance |a − b|; algorithms read prefixes as lists of reals; reason: every request lies in S, so extra inputs of the algorithm's domain are never used
--   - encoding: E[ALG]/OPT ≥ r → E[ALG] ≥ r · OPT; reason: OPT > 0 on these instances, so the two are equivalent
--   - encoding: real costs with d(x, ∅) = +∞ → costs in [0, ∞] (ENNReal), with d(x, ∅) = ⊤; reason: an algorithm that leaves the open set empty in some round pays +∞, exactly as in the source
--   - encoding: expectation over the uniformly random arrival order → finite average over all n! permutations of the labeled copies; reason: this is exactly the finite uniform law; no measurability assumption is needed
-- source:
--   Jianhao Jia, Bo Peng, Zhihao Gavin Tang, STOC 2027 submission #388 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/388.pdf, Theorem 1.4 (printed p. 2, PDF p. 4) and Theorem D.1 (printed p. 36, PDF p. 38); proof printed pp. 37–38 (PDF pp. 39–40)

import Definitions.Def_RankCutFacility_Shifted_Supplement_Online

noncomputable section
open scoped ENNReal

namespace RankCutFacility.Shifted.Supplement

/-- Theorem 1.4 / Theorem D.1 (PDF pp. 4, 38–40; printed pp. 2, 36–38). For every `C < 4` there
is one finite one-dimensional Euclidean instance — a finite `S ⊆ ℝ`, a request point `x ∈ S`, a
candidate set `F ⊆ S` with positive costs — such that every deterministic horizon-free algorithm
(one function of the revealed prefix, used for every horizon) has a horizon `n ≥ 1` at which
`n` copies of `x` in uniformly random order cost more than `C · OPT`; the same holds with every
point of `S` a feasible facility. -/
theorem unknown_horizon_lower_bound (C : ℝ) (hC : C < 4) :
    (∃ S : Finset ℝ, ∃ x ∈ S, ∃ F : Finset ℝ, F ⊆ S ∧ F.Nonempty ∧
      ∃ f : ℝ → ℝ, (∀ y ∈ F, 0 < f y) ∧
        ∀ A : OnlineAlg {y // y ∈ F} ℝ, ∃ n : ℕ, 0 < n ∧
          ENNReal.ofReal (C * offlineOpt (fun a b : ℝ => dist a b) Subtype.val
              (fun y : {y // y ∈ F} => f y) (fun _ : Fin n => x)) <
            detExpected (fun a b : ℝ => dist a b) Subtype.val
              (fun y : {y // y ∈ F} => f y) A (fun _ : Fin n => x)) ∧
    (∃ S : Finset ℝ, ∃ x ∈ S, ∃ f : ℝ → ℝ, (∀ y ∈ S, 0 < f y) ∧
        ∀ A : OnlineAlg {y // y ∈ S} ℝ, ∃ n : ℕ, 0 < n ∧
          ENNReal.ofReal (C * offlineOpt (fun a b : ℝ => dist a b) Subtype.val
              (fun y : {y // y ∈ S} => f y) (fun _ : Fin n => x)) <
            detExpected (fun a b : ℝ => dist a b) Subtype.val
              (fun y : {y // y ∈ S} => f y) A (fun _ : Fin n => x)) := by sorry

end RankCutFacility.Shifted.Supplement
