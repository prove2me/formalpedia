-- Prove2me | Theorems.Thm_PigeonholeDesign_Upper_Supplement_theorem_10
-- name    : PigeonholeDesign.Upper.Supplement.theorem_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T08:06:17.499316+00:00
-- url     : https://prove2.me/theorems/75b7893d-76fe-4ee1-af4a-57aaf730f03a
-- title:
--   Theorem 10 (corrected: rates for γ > 1 and the one-cluster case) — on clustered arrivals the pigeonhole design beats the completely randomized design
-- statement:
--   $T$ subjects arrive one at a time, $T$ even, with covariates $x_t\in[0,1]^p$ ($p\ge2$ continuous covariates, no discrete ones) chosen in advance by an adversary. The discrepancy $d_{A,B}$ of a balanced split is the minimum total Euclidean length of a perfect matching between the control group $A$ and the treated group $B$. The **matched-pair design** has discrepancy $d^{\mathrm{MP}}(x)=\min_{|A|=|B|=T/2}d_{A,B}$, the **completely randomized design** has expected discrepancy $\mathrm{ALG}^C(x)$ over a uniform control set of size $T/2$, and the **pigeonhole design** with a partition assigns each subject to the group that is short in its pigeonhole (a fair coin on ties), subject to each group holding $T/2$ subjects.
--
--   Fix $N\ge1$, $c>1$ and $\gamma\ge\underline\gamma>0$. The sequence is **clustered** if there are centres $v_1,\dots,v_N\in[0,1]^p$ with every $x_t$ in $\bigcup_n\{u:\|u-v_n\|_\infty\le\frac12T^{-\gamma}\}$. Write $L_p(T)=(\log T)^{3/2}$ if $p=2$ and $L_p(T)=1$ if $p\ge3$, and for an exponent $e$ write $e_N=e$ if $N=1$ and $e_N=\max\{e,0\}$ if $N\ge2$. Constants below depend only on $p,N,c,\gamma,\underline\gamma$; "for large $T$" means for every even $T\ge T_0$.
--
--   **Theorem 10 (p. 28), corrected.**
--   1. *($\gamma$ known.)* With $\zeta=\frac1p+\frac{p-1}p\gamma$ and the grid pigeonholes of edge $c^\zeta T^{-\zeta}$ on each axis, there is $C$ such that for large $T$ every clustered sequence gives expected discrepancy
--   $$\le C\,T^{\left(\frac{p-1}{p}(1-\gamma)\right)_N}L_p(T).$$
--   2. *($\gamma$ unknown.)* With $\underline\zeta=\frac1p+\frac{p-1}p\underline\gamma$ and the grid of edge $c^{\underline\zeta}T^{-\underline\zeta}$, there is $C$ such that for large $T$, every $\gamma'\ge\underline\gamma$ and every sequence clustered at diameter $T^{-\gamma'}$, the expected discrepancy is
--   $$\le C\,T^{\left(\frac{p-1}{p}(1-\underline\gamma)\right)_N}L_p(T).$$
--   3. *(Matched-pair design.)* There is $C$ with $d^{\mathrm{MP}}(x)\le C\,T^{\max\{1-1/p-\gamma,0\}}$ for every clustered $x$ and large $T$. If $N\ge2$ or $\gamma\le1-\frac1p$, there is $c'>0$ such that for large $T$ some clustered $x$ has $d^{\mathrm{MP}}(x)\ge c'\,T^{\max\{1-1/p-\gamma,0\}}$.
--   4. *(Completely randomized design.)* If $N\ge2$ or $\gamma\le\frac12-\frac1p$, there is $c'>0$ such that for large $T$ some clustered $x$ has
--   $$\mathrm{ALG}^C(x)\ge c'\,T^{\max\{1-1/p-\gamma,\,1/2\}}.$$
--
--   For highly clustered sequences ($\gamma>\frac12$) with at least two clusters, the pigeonhole design, which needs neither the centres nor (in part 2) the exact $\gamma$, has expected discrepancy of smaller order than the completely randomized design's $\Omega(T^{1/2})$. When $N\ge2$ and $\gamma\le1$ every corrected rate equals the printed one.
--
--   **Formalization Note** Sequences are `x : Fin T → MultiDim.Cov 0 p` and `IsClustered N γ x` is the clustered condition, including $x_t\in[0,1]^p$. The pigeonholes are the published `MultiDim.gridHole (clusterCells c (zeta p γ) T)`, with $\lceil c^{-\zeta}T^\zeta\rceil$ cells per axis, so every cell has edge at most $c^\zeta T^{-\zeta}$. `phdExp` averages the discrepancy over all $2^T$ coin vectors, `crdExp` over the $\binom{T}{T/2}$ control sets, and `mpdDisc` is the minimum over balanced splits. `γlow` is $\underline\gamma$. The theorem is one conjunction of five clauses: parts 1 and 2, the two halves of the matched-pair claim, and the completely-randomized claim.
--
--   Differences from the source:
--   - reading: 'Let there be p continuous dimensions' in §6.3 (at least two continuous covariates), 'when all the covariates are continuous' (p. 27) → hp : 2 ≤ p and covariates in MultiDim.Cov 0 p (q = 0); reason: Theorem 10 sits in §6.3 and its bullets cover p = 2 and p ≥ 3; p. 27 restricts to continuous covariates
--   - encoding: all subjects come from N clusters C(v_n, T^(−γ)) = {u : ‖u − v_n‖∞ ≤ T^(−γ)/2}, v_n ∈ [0,1]^p, unknown centres → IsClustered N γ x: covariates in [0,1]^p and ∃ v : Fin N → Fin p → ℝ in [0,1]^p with every x t within T^(−γ)/2 of some v n in every coordinate; hN : 1 ≤ N; reason: same instances; N is a fixed parameter, so the constants may depend on it
--   - encoding: pigeonholes {[0,c^ζT^(−ζ)), …, [1−c^ζT^(−ζ),1]}^p → MultiDim.gridHole (clusterCells c ζ T) with clusterCells c ζ T = ⌈c^(−ζ) T^ζ⌉; reason: the ceiling reading of the published Theorem 9 (cell edge ≤ c^ζ T^(−ζ)); equal to the printed grid when c^(−ζ)T^ζ is an integer
--   - reading: part 2: γ unknown, the design uses only γ̲ → constants C, T₀ chosen before T, then ∀ γ' ≥ γlow and every sequence clustered at γ'; reason: the design and its guarantee must not depend on the unknown true γ
--   - correction: parts 1 and 2: O(T^((p−1)(1−γ)/p)) (resp. γ̲), times (log T)^(3/2) at p = 2, for every γ → the exponent (p−1)(1−γ)/p when N = 1 and max((p−1)(1−γ)/p, 0) when N ≥ 2 (resp. with γlow); reason: for N ≥ 2 and γ > 1 the printed bound tends to 0, but x_1 at the centre 0 and x_2, …, x_T at the centre (1,…,1) is clustered and every balanced split has discrepancy ≥ √p (see DISPROOF.md); for N = 1 the printed rate holds
--   - correction: the matched-pair design has discrepancy Θ(T^(max{1−1/p−γ, 0})) for every N → upper half for every N ≥ 1; lower half under 2 ≤ N ∨ γ ≤ 1 − 1/p; reason: for N = 1 and γ > 1 − 1/p all subjects lie in one cube of edge T^(−γ) and Lemma EC.3 scaled to it gives discrepancy O(T^(1−1/p−γ)) → 0, so the Ω(1) half fails; in every other case it holds
--   - correction: the completely randomized design has expected discrepancy Ω(T^(max{1−1/p−γ, 1/2})) for every N → lower bound under 2 ≤ N ∨ γ ≤ 1/2 − 1/p; reason: for N = 1 all subjects lie in a cube of edge T^(−γ): for γ > 1/2 crdExp ≤ (√p/2)T^(1−γ) = o(T^(1/2)), and for 1/2 − 1/p < γ ≤ 1/2 a dyadic matching gives O(T^(−γ)(T^(1−1/p) + T^(1/2) log T)) = o(T^(1/2)); see DISPROOF.md
-- source:
--   Zhao and Zhou, Pigeonhole Design: Balancing Sequential Experiments from an Online Matching Perspective, arXiv:2201.12936v6, p. 28, Theorem 10 (clusters: p. 27; proof of parts 1–2: Appendix EC.13, pp. ec25–ec26)

import Mathlib
import Definitions.Def_PigeonholeDesign_MultiDim_Setting
import Definitions.Def_PigeonholeDesign_Upper_Supplement_MatchedPair
import Definitions.Def_PigeonholeDesign_Upper_Supplement_Clusters

namespace PigeonholeDesign.Upper.Supplement

theorem theorem_10 (p N : ℕ) (hp : 2 ≤ p) (hN : 1 ≤ N) (γ γlow c : ℝ) (hγlow : 0 < γlow)
    (hγ : γlow ≤ γ) (hc : 1 < c) :
    -- Part 1 (γ known): pigeonholes with `ζ = zeta p γ`
    (∃ C : ℝ, 0 < C ∧ ∃ T₀ : ℕ, ∀ T : ℕ, T₀ ≤ T → Even T →
      ∀ x : Fin T → MultiDim.Cov 0 p, IsClustered N γ x →
        PigeonholeDesign.Upper.phdExp (MultiDim.gridHole (clusterCells c (zeta p γ) T)) x
          ≤ C * (T : ℝ) ^ (if N = 1 then ((p : ℝ) - 1) / p * (1 - γ)
                            else max (((p : ℝ) - 1) / p * (1 - γ)) 0) *
              (if p = 2 then Real.log T ^ ((3 : ℝ) / 2) else 1)) ∧
    -- Part 2 (γ unknown): pigeonholes with `ζ = zeta p γlow`, uniformly over every true `γ' ≥ γlow`
    (∃ C : ℝ, 0 < C ∧ ∃ T₀ : ℕ, ∀ T : ℕ, T₀ ≤ T → Even T →
      ∀ γ' : ℝ, γlow ≤ γ' → ∀ x : Fin T → MultiDim.Cov 0 p, IsClustered N γ' x →
        PigeonholeDesign.Upper.phdExp (MultiDim.gridHole (clusterCells c (zeta p γlow) T)) x
          ≤ C * (T : ℝ) ^ (if N = 1 then ((p : ℝ) - 1) / p * (1 - γlow)
                            else max (((p : ℝ) - 1) / p * (1 - γlow)) 0) *
              (if p = 2 then Real.log T ^ ((3 : ℝ) / 2) else 1)) ∧
    -- Matched-pair design, upper half
    (∃ C : ℝ, 0 < C ∧ ∃ T₀ : ℕ, ∀ T : ℕ, T₀ ≤ T → Even T →
      ∀ x : Fin T → MultiDim.Cov 0 p, IsClustered N γ x →
        mpdDisc x ≤ C * (T : ℝ) ^ max (1 - 1 / (p : ℝ) - γ) 0) ∧
    -- Matched-pair design, lower half
    ((2 ≤ N ∨ γ ≤ 1 - 1 / (p : ℝ)) →
      ∃ c' : ℝ, 0 < c' ∧ ∃ T₀ : ℕ, ∀ T : ℕ, T₀ ≤ T → Even T →
        ∃ x : Fin T → MultiDim.Cov 0 p, IsClustered N γ x ∧
          c' * (T : ℝ) ^ max (1 - 1 / (p : ℝ) - γ) 0 ≤ mpdDisc x) ∧
    -- Completely randomized design, lower bound
    ((2 ≤ N ∨ γ ≤ 1 / 2 - 1 / (p : ℝ)) →
      ∃ c' : ℝ, 0 < c' ∧ ∃ T₀ : ℕ, ∀ T : ℕ, T₀ ≤ T → Even T →
        ∃ x : Fin T → MultiDim.Cov 0 p, IsClustered N γ x ∧
          c' * (T : ℝ) ^ max (1 - 1 / (p : ℝ) - γ) ((1 : ℝ) / 2)
            ≤ PigeonholeDesign.Upper.crdExp x) := by sorry

end PigeonholeDesign.Upper.Supplement
