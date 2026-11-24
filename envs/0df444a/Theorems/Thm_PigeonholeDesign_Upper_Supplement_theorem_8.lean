-- Prove2me | Theorems.Thm_PigeonholeDesign_Upper_Supplement_theorem_8
-- name    : PigeonholeDesign.Upper.Supplement.theorem_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T08:05:22.215649+00:00
-- url     : https://prove2.me/theorems/48a81f78-4869-4603-8df2-5e8b18872159
-- title:
--   Theorem 8 — with $p\ge2$ continuous covariates the completely randomized design has expected discrepancy $\Omega(T^{(p-1)/p})$
-- statement:
--   $T$ subjects arrive one at a time, $T$ even (p. 9). Subject $t$ carries a covariate $x_t\in\mathcal S=[0,1]^{p+q}$: $p$ continuous coordinates in $[0,1]$ and $q$ discrete coordinates, the $i$-th taking values in a finite support $S_i\subseteq[0,1]$ whose size does not depend on $T$ (pp. 10, 21). The sequence $x=(x_1,\dots,x_T)$ is chosen in advance by an adversary. For a split of the subjects into a control group $A$ and a treated group $B$ with $|A|=|B|$, the **discrepancy** $d_{A,B}$ is the minimum total Euclidean length of a perfect matching between $A$ and $B$ (display (1), p. 11).
--
--   The **completely randomized design** (Definition 2, p. 13) draws the control group uniformly among the $\binom{T}{T/2}$ subsets of size $T/2$; $\mathrm{ALG}^C(x)=\mathbb E[d_{A,B}]$ is its expected discrepancy.
--
--   Orders are worst-case over admissible arrival sequences (p. 12): "$O(f(T))$" means there are $C>0$ and $T_0$ such that for every even $T\ge T_0$ and every admissible $x$ the quantity is at most $C f(T)$; "$\Omega(f(T))$" means there are $c>0$ and $T_0$ such that for every even $T\ge T_0$ some admissible $x$ makes it at least $c f(T)$; "$\Theta$" is both. The constants depend only on the fixed parameters, never on $T$ or $x$.
--
--   **Theorem 8 (p. 25).** Let $p\ge2$ and $q\ge0$, with nonempty finite supports $S_1,\dots,S_q\subseteq[0,1]$. There are $c>0$ and $T_0$ such that for every even $T\ge T_0$ some arrival sequence $x\in(S_1\times\dots\times S_q\times[0,1]^p)^T$ has
--   $$\mathrm{ALG}^C(x)\ge c\,T^{(p-1)/p}.$$
--
--   This is a lower bound only: a matching upper bound for the completely randomized design over all arrival sequences is open (p. 25).
--
--   **Formalization Note** Subjects are indexed $0,\dots,T-1$ (`Fin T`) and an assignment is `w : Fin T → Bool` (`false` = control). The covariate space is `MultiDim.Cov q p`, the Euclidean space on $q+p$ coordinates; `MultiDim.Admissible S x` says the discrete coordinates lie in the supports $S_i$ and the continuous ones in $[0,1]$. `discrepancy` is the minimum over bijections between the two groups (program (1) is an assignment problem). `mpdDisc x` is the infimum of `discrepancy x w` over the splits with exactly $T/2$ control subjects; `crdExp x` averages `discrepancy` over the $\binom{T}{T/2}$ control sets; `phdExp hole x` averages it over all $2^T$ coin vectors, coin $t$ being used only when subject $t$ meets a tie, which gives exactly the law of Definition 3.
--
--   Differences from the source:
--   - encoding: 'on the order of O / Ω / Θ' over the worst-case oblivious adversary (p. 12) → ∃ constants > 0 and T₀ before T; ∀ even T ≥ T₀; upper halves ∀ admissible x, lower halves ∃ admissible x; reason: the paper's standing reading of the Landau orders; constants depend only on the fixed parameters
--   - encoding: covariates in S = [0,1]^(p+q) with discrete supports S_i ⊆ [0,1], Euclidean distance → x : Fin T → MultiDim.Cov q p (EuclideanSpace on Fin q ⊕ Fin p) with MultiDim.Admissible S x; subjects indexed from 0; reason: same instances; the discrete coordinates are the real support values, not indices
--   - encoding: expected discrepancy of the completely randomized design → crdExp x, the uniform average of discrepancy over the C(T, T/2) control sets; reason: Definition 2's law
--   - reading: each discrete dimension has a finite set of supports S_i (pp. 10, 21) → hypothesis ∀ i, (S i).Nonempty; reason: a support is a nonempty set of values of a covariate; with an empty S_i no admissible arrival sequence exists and the lower half would be false
-- source:
--   Zhao and Zhou, Pigeonhole Design: Balancing Sequential Experiments from an Online Matching Perspective, arXiv:2201.12936v6, p. 25, Theorem 8 (proof omitted in the paper as trivial)

import Mathlib
import Definitions.Def_PigeonholeDesign_MultiDim_Setting
import Definitions.Def_PigeonholeDesign_Upper_Supplement_MatchedPair

namespace PigeonholeDesign.Upper.Supplement

theorem theorem_8 (p q : ℕ) (hp : 2 ≤ p) (S : Fin q → Finset ℝ) (hS : ∀ i, (S i : Set ℝ) ⊆ Set.Icc 0 1)
    (hne : ∀ i, (S i).Nonempty) :
    ∃ c : ℝ, 0 < c ∧ ∃ T₀ : ℕ, ∀ T : ℕ, T₀ ≤ T → Even T →
      ∃ x : Fin T → MultiDim.Cov q p, MultiDim.Admissible S x ∧
        c * (T : ℝ) ^ (((p : ℝ) - 1) / p) ≤ PigeonholeDesign.Upper.crdExp x := by sorry

end PigeonholeDesign.Upper.Supplement
