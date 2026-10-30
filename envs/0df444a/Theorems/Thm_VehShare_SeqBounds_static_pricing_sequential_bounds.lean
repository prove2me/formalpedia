-- Prove2me | Theorems.Thm_VehShare_SeqBounds_static_pricing_sequential_bounds
-- name    : VehShare.SeqBounds.static_pricing_sequential_bounds
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T03:54:43.570278+00:00
-- url     : https://prove2.me/theorems/8f80eeba-b516-49b5-9ce3-dc28f33a7613
-- title:
--   Theorem 2: $\frac{R(q^s)}{R(q^*)}\ge\frac{R(q^s)}{R_s(q^s)}\ge B^K_i(q^s)\ge B^K_i\ge\frac{K}{N+K-1+\Lambda/\mu}$
-- statement:
--   Consider a vehicle-sharing network with $N\ge1$ locations and $K$ vehicles, demand rates $\Lambda_{ij}\ge0$, phase-type travel times with means $1/\mu_{ij}$, and per-trip rewards $I_{ij}$ with $q\,I_{ij}(q)$ concave on $[0,1]$. Let $q^s$ be an optimal solution of Problem (2) with workload budget $\Delta\ge K$, and assume $q^s$ induces a strongly connected network. Write $\Lambda/\mu=\sum_{(i,j)\in\mathcal A}\Lambda_{ij}/\mu_{ij}$, $\lambda/\mu=\sum_{(i,j)\in\mathcal A}\Lambda_{ij}q^s_{ij}/\mu_{ij}$, and define for $i\ge1$
--
--   $$
--   B^K_i(q^s)=\frac{K}{N+K-1+\frac{\lambda}{\mu}\big(1-B^{K-1}_{i-1}(q^s)\big)},\qquad B^K_i=\frac{K}{N+K-1+\frac{\Lambda}{\mu}\big(1-B^{K-1}_{i-1}\big)},
--   $$
--
--   with $B^j_0(q^s)=B^j_0=0$. Let $R(q^*)$ be the supremum of the long-run reward $R(q,\pi)$ over all dynamic policies $q$ and stationary distributions $\pi$. Then:
--
--   1. every dynamic policy $q$ and every stationary distribution $\pi$ of its chain satisfy $R(q,\pi)\le R_s(q^s)$;
--   2. the chain of the static policy $q^s$ has a stationary distribution, and every stationary distribution $\pi$ of it satisfies $B^K_i(q^s)\,R_s(q^s)\le R(q^s,\pi)$ for $i=1,\dots,K$;
--   3. if $R_s(q^s)>0$, every such $\pi$ satisfies, for $i=1,\dots,K$,
--   $$
--   \frac{R(q^s,\pi)}{R(q^*)}\ \ge\ \frac{R(q^s,\pi)}{R_s(q^s)}\ \ge\ B^K_i(q^s);
--   $$
--   4. $B^K_i(q^s)\ge B^K_i\ge\dfrac{K}{N+K-1+\Lambda/\mu}$ for $i=1,\dots,K$;
--   5. if $\Lambda/\mu>0$, then $B^K_{i+1}>B^K_i$ for $i=1,\dots,K-1$.
--
--   The static policy obtained from the fluid problem therefore earns a guaranteed fraction of the optimal dynamic reward, and the sequence of guarantees improves strictly with each iteration of the availability recursion, the last one, $B^K_K(q^s)$, being the availability itself.
--
--   Differences from the source:
--   - reading: trip durations i.i.d. with a general distribution with rational Laplace transform and mean 1/μij, represented by a network of exponential stages (p. 4) → a phase-type law per pair: finitely many stages, entry probabilities β (total ≤ 1; the defect is a zero-length trip), rates r between stages, exit rates e, an exit reachable from every stage; 1/μij = β(−T)⁻¹𝟙; reason: the paper's state counts vehicles at each stage of the transit queue (footnote 1), so the model exists exactly for laws with such a stage network, i.e. phase-type laws; the general (not only Coxian) form is taken
--   - encoding: demand, prices, rewards and travel data on the pairs (i,j) ∈ 𝒜 (Λij > 0) → all of them given on every pair of locations; reason: pairs with Λij = 0 enter every rate, sum and constraint with factor 0; no instance changes
--   - encoding: prices pij with acceptance fractions qij = 1 − Fij(pij) (p. 5) → the fractions q ∈ [0,1] and the per-trip rewards Iij(q) as primitives, q·Iij(q) concave on [0,1]; reason: the paper reformulates the policy in terms of the quantiles q (p. 5); concavity of q·I is its only requirement
--   - reading: R(q*), the reward of an optimal dynamic policy under its steady-state probability → Ropt, the supremum of R(q,π) over every dynamic policy q and every stationary distribution π of its chain; reason: a state-dependent policy can make the chain reducible, so π need not be unique; taking every stationary law makes R(q*) as large as possible, the stronger reading
--   - reading: R(q^s), the reward of the static policy under its steady-state probability → a stationary distribution of the static chain exists, and every stationary distribution π satisfies the bounds with R(q^s, π); reason: the static chain has a unique stationary law (p. 6); the existence clause keeps the universal statement from being vacuous and nothing rests on uniqueness
--   - encoding: the ratio chain R(q^s)/R(q*) ≥ R(q^s)/Rs(q^s) ≥ B^K_i(q^s) → R(q,π) ≤ Rs(q^s) and B^K_i(q^s)·Rs(q^s) ≤ R(q^s,π) unconditionally, and the ratios themselves under 0 < Rs(q^s); reason: if Rs(q^s) = 0 then R(q*) = 0 too, so every ratio of the paper is 0/0; the hypothesis excludes only undefined cases
--   - encoding: Λ/μ with Λ = Σ_𝒜 Λij and 1/μ = Σ_𝒜 Λij/(Λ μij) (Theorem 1, p. 7) → LamOverMu = Σ_{i,j} Λij · meanTime ij; reason: equals Λ·(1/μ) when Λ > 0; when Λ = 0 the paper's 1/μ is 0/0 and the sum is 0
--   - encoding: N locations (N ≥ 1) → at least one location ([Nonempty P.L]); reason: with no location and K ≥ 1 there is no state; the paper has N ≥ 1 locations
--   - encoding: B^j_0 = 0 for j = 1, …, K, and B^K_i defined for i = 1, …, K → Bseq N W j i on all indices with Bseq N W j 0 = 0 for every j (including B^0_0 = 0); natural-number index j − 1, real denominator N + j − 1 + W(1 − ·); reason: the paper's proof uses B^1_1 = 1/(N + Λ/μ), i.e. B^0_0 = 0; values outside the paper's ranges are not used by the clauses that cite them
--   - encoding: Moreover, B^K_{i+1} > B^K_i for all i = 1, …, K − 1 → the same under the hypothesis 0 < Λ/μ; reason: the paper's 1/μ is defined only for Λ > 0 and every mean travel time is positive, so Λ/μ > 0 throughout the paper; at Λ/μ = 0 the claim is false (N = 1, K = 2: B^2_1 = B^2_2 = 1)
--   - generalization: the network generated by 𝒩 and 𝒜 is strongly connected (p. 4, without loss of generality) → not assumed separately; reason: it follows from the strong connectivity of the flow of q^s, whose arcs lie in 𝒜; the paper's instances are a special case
--   - reading: "q^s induces a strongly connected network" (p. 6) → FlowStronglyConnected: in the digraph on all locations with an arc a → b whenever Λab q^s_ab > 0, every location reaches every location; reason: the network induced by a price vector is the graph of its positive demand flows; with one location the condition holds trivially
-- source:
--   Benjaafar, Shen, Pricing in On-Demand (and One-Way) Vehicle Sharing Networks, SSRN 3998297 (version of 2023-01-10), https://ssrn.com/abstract=3998297, Theorem 2, p. 9 (proof pp. 9–10)

import Mathlib
import Definitions.Def_VehShare_SeqBounds_IsOptimal2
import Definitions.Def_VehShare_SeqBounds_staticPolicy
import Definitions.Def_VehShare_SeqBounds_Ropt
import Definitions.Def_VehShare_SeqBounds_LamOverMu
import Definitions.Def_VehShare_SeqBounds_FlowStronglyConnected
import Definitions.Def_VehShare_SeqBounds_Bseq

namespace VehShare.SeqBounds

/-- **Theorem 2: sequential lower bounds for static pricing.**
Benjaafar, Shen, *Pricing in On-Demand (and One-Way) Vehicle Sharing Networks*, SSRN 3998297
(version of 2023-01-10), Theorem 2, p. 9 (proof pp. 9–10): "`R(q^s)/R(q∗) ≥ R(q^s)/Rs(q^s) ≥ B^K_i(q^s) ≥ B^K_i
≥ K/(N+K−1+Λ/µ)` ... for all `i = 1, 2, ···, K` ... Moreover, `B^K_{i+1} > B^K_i` for all
`i = 1, 2, ···, K − 1`".

Let `q^s` be an optimal solution of Problem (2) with `Δ ≥ K` that induces a strongly connected
network; write `N = |𝒩|`, `λ/μ` for the workload of `q^s`, `B^K_i(q^s) = Bseq N (λ/μ) K i` and
`B^K_i = Bseq N (Λ/μ) K i`. Then:
* (a) every dynamic policy `q` and every stationary law `π` of its chain earn `R(q, π) ≤ R_s(q^s)`;
* (b) the static chain has a stationary law, and every stationary law `π` of it earns
  `B^K_i(q^s) · R_s(q^s) ≤ R(q^s, π)` for `1 ≤ i ≤ K`;
* (d) if `R_s(q^s) > 0`, then every such `π` satisfies `R(q^s,π)/R_s(q^s) ≤ R(q^s,π)/R(q*)` and
  `B^K_i(q^s) ≤ R(q^s,π)/R_s(q^s)` for `1 ≤ i ≤ K`, where `R(q*)` is `Ropt P K`;
* (c) `B^K_i ≤ B^K_i(q^s)` and `K/(N + K − 1 + Λ/μ) ≤ B^K_i` for `1 ≤ i ≤ K`;
* (e) if `Λ/μ > 0`, then `B^K_i < B^K_{i+1}` for `1 ≤ i ≤ K − 1`.

**Formalization Note.**
* Reading 1: travel times are phase-type (`Instance`). Reading 2: `R(q*)` is the supremum of
  `R(q, π)` over every dynamic policy and every stationary law (`Ropt`); the set is nonempty (the
  zero policy with a point mass on a state with every vehicle parked at one location) and bounded
  above by clause (a), so the `sSup` is the true supremum.
* Reading 3: `R(q^s)` is read as "a stationary law of the static chain exists, and every one
  satisfies the bounds". Encoding 4: (a)–(c) are the multiplicative form; (d) adds the paper's
  ratios under `R_s(q^s) > 0` (if `R_s(q^s) = 0`, every ratio of the paper is `0/0`).
* Encoding 5: `Λ/μ = ∑ Λ_ij/μ_ij` (`LamOverMu`). Encodings 6, 7: data on all pairs, quantile prices.
  Encoding 8: at least one location. Reading 9: `Bseq` with `B^0_0 = 0`; every clause restricts to the
  paper's ranges. Encoding 10: `Λ/μ > 0` on clause (e) only. Generalization 11: strong connectivity of
  `(𝒩, 𝒜)` is not assumed (it follows from that of the flow of `q^s`). Reading 12:
  `FlowStronglyConnected`. Every `K − 1` is computed in `ℝ`. -/
theorem static_pricing_sequential_bounds (P : Instance) [Nonempty P.L] (K : ℕ) (Δ : ℝ)
    (hΔ : (K : ℝ) ≤ Δ) (qs : P.L → P.L → ℝ) (hqs : IsOptimal2 P Δ qs)
    (hsc : FlowStronglyConnected P qs) :
    -- (a) Proposition 1: every policy and every stationary law earn at most `R_s(q^s)`
    (∀ (q : Policy P K) (π : State P K → ℝ), IsStationary q π → reward q π ≤ Rs P qs) ∧
    -- (b) the static chain has a stationary law ...
    (∃ π : State P K → ℝ, IsStationary (staticPolicy P K qs hqs.1.1) π) ∧
    -- ... and every one meets the bounds
    (∀ π : State P K → ℝ, IsStationary (staticPolicy P K qs hqs.1.1) π →
      (∀ i : ℕ, 1 ≤ i → i ≤ K →
        Bseq (Fintype.card P.L) (workload P qs) K i * Rs P qs ≤
          reward (staticPolicy P K qs hqs.1.1) π) ∧
      -- (d) the paper's ratio chain, with `R(q*) = Ropt P K`
      (0 < Rs P qs →
        reward (staticPolicy P K qs hqs.1.1) π / Rs P qs ≤
            reward (staticPolicy P K qs hqs.1.1) π / Ropt P K ∧
          ∀ i : ℕ, 1 ≤ i → i ≤ K →
            Bseq (Fintype.card P.L) (workload P qs) K i ≤
              reward (staticPolicy P K qs hqs.1.1) π / Rs P qs)) ∧
    -- (c) `B^K_i(q^s) ≥ B^K_i ≥ K/(N + K − 1 + Λ/μ)`
    (∀ i : ℕ, 1 ≤ i → i ≤ K →
      Bseq (Fintype.card P.L) (LamOverMu P) K i ≤ Bseq (Fintype.card P.L) (workload P qs) K i ∧
        (K : ℝ) / ((Fintype.card P.L : ℝ) + (K : ℝ) - 1 + LamOverMu P) ≤
          Bseq (Fintype.card P.L) (LamOverMu P) K i) ∧
    -- (e) Moreover, `B^K_{i+1} > B^K_i`
    (0 < LamOverMu P → ∀ i : ℕ, 1 ≤ i → i + 1 ≤ K →
      Bseq (Fintype.card P.L) (LamOverMu P) K i < Bseq (Fintype.card P.L) (LamOverMu P) K (i + 1)) := by sorry

end VehShare.SeqBounds
