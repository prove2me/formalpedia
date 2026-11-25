-- Prove2me | Theorems.Thm_PigeonholeDesign_Upper_Supplement_theorem_1
-- name    : PigeonholeDesign.Upper.Supplement.theorem_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-24T08:00:53.634603+00:00
-- url     : https://prove2.me/theorems/62872a7e-508e-42ef-a283-46e4e221afb2
-- title:
--   Theorem 1 (corrected: some support has two values) — with only discrete covariates the matched-pair design has discrepancy $\Theta(1)$
-- statement:
--   $T$ subjects arrive one at a time, $T$ even (p. 9). Subject $t$ carries a covariate $x_t\in\mathcal S=[0,1]^{p+q}$: $p$ continuous coordinates in $[0,1]$ and $q$ discrete coordinates, the $i$-th taking values in a finite support $S_i\subseteq[0,1]$ whose size does not depend on $T$ (pp. 10, 21). The sequence $x=(x_1,\dots,x_T)$ is chosen in advance by an adversary. For a split of the subjects into a control group $A$ and a treated group $B$ with $|A|=|B|$, the **discrepancy** $d_{A,B}$ is the minimum total Euclidean length of a perfect matching between $A$ and $B$ (display (1), p. 11).
--
--   The **matched-pair design** (Definition 1, p. 12) knows all covariates in advance and uses the best balanced split, so its discrepancy is
--   $$d^{\mathrm{MP}}(x)=\min_{|A|=|B|=T/2} d_{A,B};$$
--   randomly swapping the two subjects of each matched pair does not change it.
--
--   Orders are worst-case over admissible arrival sequences (p. 12): "$O(f(T))$" means there are $C>0$ and $T_0$ such that for every even $T\ge T_0$ and every admissible $x$ the quantity is at most $C f(T)$; "$\Omega(f(T))$" means there are $c>0$ and $T_0$ such that for every even $T\ge T_0$ some admissible $x$ makes it at least $c f(T)$; "$\Theta$" is both. The constants depend only on the fixed parameters, never on $T$ or $x$.
--
--   **Theorem 1 (p. 22).** Let $p=0$ and $q\ge1$, with nonempty supports $S_1,\dots,S_q\subseteq[0,1]$, at least one of which has two distinct values. There are constants $0<c\le C$ and $T_0$ such that for every even $T\ge T_0$:
--   1. every arrival sequence $x\in(S_1\times\dots\times S_q)^T$ has $d^{\mathrm{MP}}(x)\le C$;
--   2. some arrival sequence $x\in(S_1\times\dots\times S_q)^T$ has $d^{\mathrm{MP}}(x)\ge c$.
--
--   That is, $\max_x d^{\mathrm{MP}}(x)=\Theta(1)$. With finitely many covariate values, an offline matching leaves only a bounded number of subjects whose partner has a different covariate.
--
--   **Formalization Note** Subjects are indexed $0,\dots,T-1$ (`Fin T`) and an assignment is `w : Fin T → Bool` (`false` = control). The covariate space is `MultiDim.Cov q p`, the Euclidean space on $q+p$ coordinates; `MultiDim.Admissible S x` says the discrete coordinates lie in the supports $S_i$ and the continuous ones in $[0,1]$. `discrepancy` is the minimum over bijections between the two groups (program (1) is an assignment problem). `mpdDisc x` is the infimum of `discrepancy x w` over the splits with exactly $T/2$ control subjects; `crdExp x` averages `discrepancy` over the $\binom{T}{T/2}$ control sets; `phdExp hole x` averages it over all $2^T$ coin vectors, coin $t$ being used only when subject $t$ meets a tie, which gives exactly the law of Definition 3.
--
--   Differences from the source:
--   - encoding: 'on the order of O / Ω / Θ' over the worst-case oblivious adversary (p. 12) → ∃ constants > 0 and T₀ before T; ∀ even T ≥ T₀; upper halves ∀ admissible x, lower halves ∃ admissible x; reason: the paper's standing reading of the Landau orders; constants depend only on the fixed parameters
--   - encoding: covariates in S = [0,1]^(p+q) with discrete supports S_i ⊆ [0,1], Euclidean distance → x : Fin T → MultiDim.Cov q p (EuclideanSpace on Fin q ⊕ Fin p) with MultiDim.Admissible S x; subjects indexed from 0; reason: same instances; the discrete coordinates are the real support values, not indices
--   - encoding: the matched-pair design's discrepancy d_{A*,B*} (Definition 1, display (2)) after the random swaps inside the pairs → mpdDisc x, the infimum of discrepancy x w over the splits with exactly T/2 control subjects; reason: the swaps keep the optimal matching feasible, so the discrepancy after them equals the minimum in (2)
--   - reading: each discrete dimension has a finite set of supports S_i (pp. 10, 21) → hypothesis ∀ i, (S i).Nonempty; reason: a support is a nonempty set of values of a covariate; with an empty S_i no admissible arrival sequence exists and the lower half would be false
--   - correction: p = 0, q ≥ 1 with arbitrary finite supports → hypothesis ∃ i, 2 ≤ (S i).card; reason: if every S_i is a singleton all covariates coincide and every discrepancy is 0, so the Θ lower half fails (counterexample q = 1, S_1 = {0}); p. 10 rescales each support to [0,1], which gives two values
-- source:
--   Zhao and Zhou, Pigeonhole Design: Balancing Sequential Experiments from an Online Matching Perspective, arXiv:2201.12936v6, p. 22, Theorem 1 (proof: Appendix EC.8, p. ec16)

import Mathlib
import Definitions.Def_PigeonholeDesign_MultiDim_Setting
import Definitions.Def_PigeonholeDesign_Upper_Supplement_MatchedPair

namespace PigeonholeDesign.Upper.Supplement

theorem theorem_1 (q : ℕ) (hq : 1 ≤ q) (S : Fin q → Finset ℝ) (hS : ∀ i, (S i : Set ℝ) ⊆ Set.Icc 0 1)
    (hne : ∀ i, (S i).Nonempty)
    (h2 : ∃ i, 2 ≤ (S i).card) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∃ T₀ : ℕ, ∀ T : ℕ, T₀ ≤ T → Even T →
      (∀ x : Fin T → MultiDim.Cov q 0, MultiDim.Admissible S x → mpdDisc x ≤ C) ∧
      (∃ x : Fin T → MultiDim.Cov q 0, MultiDim.Admissible S x ∧ c ≤ mpdDisc x) := by sorry

end PigeonholeDesign.Upper.Supplement
