-- Prove2me | Theorems.Thm_PigeonholeDesign_Upper_Supplement_theorem_6
-- name    : PigeonholeDesign.Upper.Supplement.theorem_6
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-24T08:04:08.020812+00:00
-- url     : https://prove2.me/theorems/06f4c060-da1b-486d-a4b7-92de7802b841
-- title:
--   Theorem 6 — supports $\times$ $T^{-1/2}$-intervals give $O(T^{1/4}(\log T)^{1/2})$; every pigeonhole design suffers $\Omega(T^{1/4})$
-- statement:
--   $T$ subjects arrive one at a time, $T$ even (p. 9). Subject $t$ carries a covariate $x_t\in\mathcal S=[0,1]^{p+q}$: $p$ continuous coordinates in $[0,1]$ and $q$ discrete coordinates, the $i$-th taking values in a finite support $S_i\subseteq[0,1]$ whose size does not depend on $T$ (pp. 10, 21). The sequence $x=(x_1,\dots,x_T)$ is chosen in advance by an adversary. For a split of the subjects into a control group $A$ and a treated group $B$ with $|A|=|B|$, the **discrepancy** $d_{A,B}$ is the minimum total Euclidean length of a perfect matching between $A$ and $B$ (display (1), p. 11).
--
--   The **pigeonhole design** (Definition 3, p. 16) with a partition of the covariate space into pigeonholes assigns each arriving subject as follows: if either group already has $T/2$ subjects, the subject joins the other group; otherwise, if its pigeonhole holds fewer control than treated subjects it joins control, if fewer treated than control it joins treatment, and on a tie it flips a fair coin. Its expected discrepancy is the average of $d_{A,B}$ over the coins.
--
--   Orders are worst-case over admissible arrival sequences (p. 12): "$O(f(T))$" means there are $C>0$ and $T_0$ such that for every even $T\ge T_0$ and every admissible $x$ the quantity is at most $C f(T)$; "$\Omega(f(T))$" means there are $c>0$ and $T_0$ such that for every even $T\ge T_0$ some admissible $x$ makes it at least $c f(T)$; "$\Theta$" is both. The constants depend only on the fixed parameters, never on $T$ or $x$.
--
--   **Theorem 6 (p. 24).** Let $p=1$ and $q\ge0$, with nonempty finite supports $S_1,\dots,S_q\subseteq[0,1]$.
--   1. *(Upper bound.)* Use the pigeonholes
--   $$\mathcal P(\mathcal S)=S_1\times\dots\times S_q\times\big\{[0,T^{-1/2}),[T^{-1/2},2T^{-1/2}),\dots,[1-T^{-1/2},1]\big\}.$$
--   There are $C>0$ and $T_0$ such that for every even $T\ge T_0$ and every arrival sequence $x\in(S_1\times\dots\times S_q\times[0,1])^T$ the pigeonhole design's expected discrepancy is at most
--   $$C\,T^{1/4}(\log T)^{1/2}.$$
--   2. *(Lower bound for every partition.)* There are $c>0$ and $T_0$ such that for every even $T\ge T_0$ and **every** finite partition of the covariate space into pigeonholes, some arrival sequence $x\in(S_1\times\dots\times S_q\times[0,1])^T$ gives that pigeonhole design an expected discrepancy at least $c\,T^{1/4}$.
--
--   The two halves show that, up to the logarithm, the uniform grid of $\sqrt T$ intervals is the best any pigeonhole design can do with one continuous covariate. $\log$ is the natural logarithm.
--
--   **Formalization Note** Subjects are indexed $0,\dots,T-1$ (`Fin T`) and an assignment is `w : Fin T → Bool` (`false` = control). The covariate space is `MultiDim.Cov q p`, the Euclidean space on $q+p$ coordinates; `MultiDim.Admissible S x` says the discrete coordinates lie in the supports $S_i$ and the continuous ones in $[0,1]$. `discrepancy` is the minimum over bijections between the two groups (program (1) is an assignment problem). `mpdDisc x` is the infimum of `discrepancy x w` over the splits with exactly $T/2$ control subjects; `crdExp x` averages `discrepancy` over the $\binom{T}{T/2}$ control sets; `phdExp hole x` averages it over all $2^T$ coin vectors, coin $t$ being used only when subject $t$ meets a tie, which gives exactly the law of Definition 3. The upper half's pigeonholes are the published `MultiDim.gridHole ⌈T^{1/2}⌉` on `Cov q 1`: exact discrete values times $m=\lceil T^{1/2}\rceil$ cells $[k/m,(k+1)/m)$, the last closed, each of length $1/m\le T^{-1/2}$ (the ceiling reading of Lemma 3 and Corollary 1). In the lower half a finite partition is any map `hole : Cov q 1 → Fin K`, for every $K$; the constant $c$ does not depend on $K$ or on the partition.
--
--   Differences from the source:
--   - encoding: 'on the order of O / Ω / Θ' over the worst-case oblivious adversary (p. 12) → ∃ constants > 0 and T₀ before T; ∀ even T ≥ T₀; upper halves ∀ admissible x, lower halves ∃ admissible x; reason: the paper's standing reading of the Landau orders; constants depend only on the fixed parameters
--   - encoding: covariates in S = [0,1]^(p+q) with discrete supports S_i ⊆ [0,1], Euclidean distance → x : Fin T → MultiDim.Cov q p (EuclideanSpace on Fin q ⊕ Fin p) with MultiDim.Admissible S x; subjects indexed from 0; reason: same instances; the discrete coordinates are the real support values, not indices
--   - encoding: expected discrepancy of the pigeonhole design with fair coins on ties → phdExp hole x, the average of discrepancy over all 2^T coin vectors (coin t used only at a tie of subject t); reason: gives exactly Definition 3's law
--   - encoding: intervals [0,T^(−1/2)), …, [1−T^(−1/2),1] (assumes T^(1/2) an integer) → MultiDim.gridHole ⌈T^(1/2)⌉ (m = ⌈T^(1/2)⌉ cells of length 1/m ≤ T^(−1/2), last cell closed); reason: the ceiling reading of the published Lemma 3 / Corollary 1; equal to the printed partition when T^(1/2) is an integer
--   - encoding: 'any pigeonhole design' (Definition 3: a K-partition of the covariate space) → ∀ K, ∀ hole : MultiDim.Cov q 1 → Fin K, with c chosen before T, K and hole; reason: a finite partition is labelled by Fin K; its values outside [0,1]^(q+1) are never used
--   - reading: each discrete dimension has a finite set of supports S_i (pp. 10, 21) → hypothesis ∀ i, (S i).Nonempty; reason: a support is a nonempty set of values of a covariate; with an empty S_i no admissible arrival sequence exists and the lower half would be false
-- source:
--   Zhao and Zhou, Pigeonhole Design: Balancing Sequential Experiments from an Online Matching Perspective, arXiv:2201.12936v6, p. 24, Theorem 6 (proof: Appendix EC.9, pp. ec17–ec18)

import Mathlib
import Definitions.Def_PigeonholeDesign_MultiDim_Setting
import Definitions.Def_PigeonholeDesign_Upper_Supplement_MatchedPair

namespace PigeonholeDesign.Upper.Supplement

theorem theorem_6 (q : ℕ) (S : Fin q → Finset ℝ) (hS : ∀ i, (S i : Set ℝ) ⊆ Set.Icc 0 1)
    (hne : ∀ i, (S i).Nonempty) :
    (∃ C : ℝ, 0 < C ∧ ∃ T₀ : ℕ, ∀ T : ℕ, T₀ ≤ T → Even T →
      ∀ x : Fin T → MultiDim.Cov q 1, MultiDim.Admissible S x →
        PigeonholeDesign.Upper.phdExp
            (MultiDim.gridHole (q := q) (p := 1) ⌈(T : ℝ) ^ ((1 : ℝ) / 2)⌉₊) x
          ≤ C * ((T : ℝ) ^ ((1 : ℝ) / 4) * Real.sqrt (Real.log T))) ∧
    (∃ c : ℝ, 0 < c ∧ ∃ T₀ : ℕ, ∀ T : ℕ, T₀ ≤ T → Even T →
      ∀ (K : ℕ) (hole : MultiDim.Cov q 1 → Fin K),
        ∃ x : Fin T → MultiDim.Cov q 1, MultiDim.Admissible S x ∧
          c * (T : ℝ) ^ ((1 : ℝ) / 4) ≤ PigeonholeDesign.Upper.phdExp hole x) := by sorry

end PigeonholeDesign.Upper.Supplement
