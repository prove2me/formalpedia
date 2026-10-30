-- Prove2me | Theorems.Thm_RideHailingAV_PureHV_proposition_1_pure_hv_equilibrium
-- name    : RideHailingAV.PureHV.proposition_1_pure_hv_equilibrium
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-29T23:29:43.185995+00:00
-- url     : https://prove2.me/theorems/f1aea28d-f756-461c-9178-52b92648059b
-- title:
--   Proposition 1 — existence, uniqueness and comparative statics of the pure-HV maximal stable equilibrium
-- statement:
--   Consider a pure-HV market with ETA function $t_1(s)=as^{-r}$ ($a>0$, $0\le r<1$), trip time $t_2>0$, rider values uniform on $[0,V]$ ($V>0$), and HV supply curve $w(n_{HV})=w_0+\alpha n_{HV}$ with $w_0>0$, $\alpha\ge0$. Consider $I$ demand scenarios with potential demand masses $0<m_1<m_2<\dots<m_I$, each satisfying Assumption 2 (18). Then in each scenario $i$ there is a unique maximal stable equilibrium $d^*_{HV,i}$, with price $p^*_{HV,i}=p_i(d^*_{HV,i})$, fleet size $n^*_{HV,i}=\underline n(d^*_{HV,i})$ and utilization $u^*_{HV,i}=\bar u(d^*_{HV,i})$. Moreover:
--
--   1. the equilibrium demand satisfies
--   $$r_i(d^*_{HV,i})=w(n^*_{HV,i})\,n^*_{HV,i},\qquad n^*_{HV,i}=\tilde a\,(d^*_{HV,i})^{1/(r+1)}+t_2\,d^*_{HV,i};\qquad(15)$$
--   2. $d^*_{HV,i}$ is strictly increasing in $i$ (in the mass $m_i$);
--   3. if $r>0$, the utilization $u^*_{HV,i}=d^*_{HV,i}t_2/\underline n(d^*_{HV,i})$ (16) is strictly increasing in $i$; if $r=0$, it is the same in every scenario;
--   4. the fleet size $n^*_{HV,i}$ is strictly increasing in $i$;
--   5. the equilibrium price is
--   $$p^*_{HV,i}=\frac{w(n^*_{HV,i})}{u^*_{HV,i}}.\qquad(17)$$
--
--   Furthermore, the equilibrium price $p^*_{HV,i}$ may be increasing, decreasing, or non-monotonic in $m_i$: there is a market satisfying all the hypotheses above (with $I\ge2$ scenarios) whose maximal stable equilibrium prices $p^*_{HV,i}=p_i(d^*_{HV,i})$ are strictly increasing in $i$, there is one where they are strictly decreasing in $i$, and there is one where they are neither non-decreasing nor non-increasing in $i$.
--
--   A denser market serves more demand with a larger HV fleet, and with a density effect ($r>0$) it uses that fleet more efficiently. These comparative statics are the baseline against which the paper measures the introduction of autonomous vehicles.
--
--   This item covers the whole proposition: the existence and uniqueness statement, Items 1–4, and both sentences of Item 5. The Lean statement is a conjunction of a universally quantified part (existence, uniqueness, Items 1–4 and (17)) and three closed existential parts (the possibility claim of Item 5).
--
--   **Formalization Note** The equilibrium quadruple $(d^*,p^*,n^*,u^*)$ is determined by its demand, so the statement exhibits $d^*$ and writes the others as $p_i(d^*)$, $\underline n(d^*)$, $\bar u(d^*)$. Scenarios are indexed by $\mathrm{Fin}\ I$; for $I=0$ the statement is trivially true, as in the paper.
--
--   Differences from the source:
--   - reading: Assumption 2, stated after the proposition → a hypothesis of the theorem for every scenario, in its form (18) (IsLooseMarket), not as (33); reason: the proof (B.1.1, p. 42) invokes it and Items 2 and 4 fail without it (thin market: V = 1, a = 1, r = 0.5, t₂ = 0.5, w₀ = 5, α = 0 gives d* = 0 in every scenario); p. 7 announces it as a standing assumption of the model ("we assume the labor market is 'loose' … (see Assumption 2 below)"); (33) is strictly stronger than (18) at d* = mᵢ/2
--   - reading: Definition 1: there is no ε > 0 such that rᵢ(d − ε) < w(n(d − ε))n(d − ε) and rᵢ(d + ε) > w(n(d + ε))n(d + ε) → no ε > 0 with 0 ≤ d − ε and d + ε ≤ m satisfies both inequalities (IsStableHVEquilibrium); reason: keeps the arguments in the demand domain [0, mᵢ] of (3); the maximal stable equilibrium is the largest solution of (13) in [0, mᵢ] under both readings, since beyond mᵢ revenue is negative and cost positive
--   - encoding: a unique maximal stable equilibrium (d*, p*, n*, u*) → a unique d* with p* = pᵢ(d*), n* = n(d*), u* = ū(d*); reason: the paper defines p*, n*, u* from d* ((47), (15), (16)), so uniqueness of the quadruple is uniqueness of d*
--   - encoding: n(d) = min_s {s + d(t₁(s) + t₂)} → sInf of s + d(a s^(−r) + t₂) over s > 0 (minSupply); reason: the values are equal (Lemma 1); s > 0 avoids the undefined t₁(0) for r > 0, and at r = 0 the infimum over s > 0 equals the minimum at s = 0
--   - encoding: equilibrium demand rates → IsHVEquilibrium requires 0 ≤ d ≤ m; reason: (3) defines pᵢ on [0, mᵢ] only
--   - reading: 'increasing' in Items 2–4; 'constant in i' in Item 3 → strictly increasing (StrictMono); equal across all scenarios i, j; reason: the proof shows strict inequalities (43), (44), (46); this is the stronger reading
--   - generalization: Assumption 1 (c_v + c_f < w₀ with c_f, c_v > 0, p. 7) → 0 < w₀; reason: the pure-HV market involves no AV and uses Assumption 1 only through w₀ > 0, which Assumption 1 implies, so the statement specializes to the paper's
--   - encoding: the model constants a, t₂, V and masses mᵢ → explicit hypotheses 0 < a, 0 < t₂, 0 < V, 0 < mᵢ; reason: implicit in the model: ã > 0 is stated on p. 12 and ã > 0 iff a > 0; t₂ is a trip time; V is the top of the value support; (3) divides by mᵢ
--   - encoding: I demand scenarios m₁ < … < m_I → m : Fin I → ℝ strictly monotone, I = 0 allowed; reason: the paper puts no lower bound on I; I = 0 is vacuous
--   - reading: Item 5, the equilibrium price may be increasing, decreasing, or non-monotonic in mᵢ → three existential conjuncts: some admissible market with I ≥ 2 has strictly increasing prices p*ᵢ, some has strictly decreasing prices, some has prices that are neither Monotone nor Antitone; reason: 'may be' is a possibility claim over the class of markets (B.1.6 gives r = 0, α > 0 for increasing and r > 0, α = 0 for decreasing); strict monotonicity is the stronger reading; I ≥ 2 keeps the monotone cases from being met by a single scenario
-- source:
--   Lian, van Ryzin, Capturing the Benefits of Autonomous Vehicles in Ride-Hailing: The Role of Market Configuration, SSRN 3716491 (version of 23 August 2023), Proposition 1, p. 14; Definition 1, p. 13; Assumption 2, eq. (18), p. 15; proof in Appendix B.1, pp. 42–45

import Mathlib
import Definitions.Def_RideHailingAV_PureHV_Market
import Definitions.Def_RideHailingAV_PureHV_aTilde
import Definitions.Def_RideHailingAV_PureHV_util
import Definitions.Def_RideHailingAV_PureHV_IsLooseMarket

namespace RideHailingAV.PureHV

/-- **Proposition 1 — the pure-HV maximal stable equilibrium.** Lian, van Ryzin, *Capturing the Benefits of Autonomous Vehicles in Ride-Hailing: The Role of
Market Configuration*, SSRN 3716491 (version of 23 August 2023),
Proposition 1, p. 14, with Definition 1 (p. 13), the maximal-stable convention (p. 14) and
Assumption 2, eq. (18) (p. 15); proof in Appendix B.1, pp. 42–45.

Consider a pure-HV market with supply curve `w(n_HV) = w₀ + α n_HV`, `α ≥ 0`, and `I` demand
scenarios with potential demand masses `m₁ < m₂ < … < m_I`, each satisfying Assumption 2. Then in
each scenario `i` there is a unique maximal stable equilibrium `d*_i` (with `p*_i = p_i(d*_i)`,
`n*_i = n(d*_i)`, `u*_i = ū(d*_i)`), and:
1. `r_i(d*_i) = w(n*_i) n*_i` (15), with `n*_i = n(d*_i) = ã (d*_i)^(1/(r+1)) + t₂ d*_i`;
2. `d*_i` is strictly increasing in `i`;
3. if `r > 0`, `u*_i` is strictly increasing in `i`; if `r = 0`, `u*_i` is constant in `i`;
4. `n*_i` is strictly increasing in `i`;
5. (17) `p*_i = w(n*_i) / u*_i`; and the equilibrium price "may be increasing, decreasing, or
   non-monotonic in `m_i`": each of the three happens for some admissible market (the last three
   conjuncts of the statement, quantified over markets and scenario families).

**Formalization Note.** The equilibrium quadruple is determined by its demand: `p* = p_i(d*)`
(eq. (47), p. 45), `n* = n(d*)`, `u* = ū(d*)`. Assumption 2 is a hypothesis (the proof in B.1.1
invokes it; Items 2 and 4 fail without it). `w₀ > 0` is the consequence of Assumption 1 that the
pure-HV market uses. Item 5's first sentence is a possibility claim about the class of markets,
so it is the last three, closed conjuncts: for each behaviour there are parameters (`a, t₂, V, w₀ > 0`,
`0 ≤ r < 1`, `α ≥ 0`), `I ≥ 2` strictly increasing positive masses satisfying Assumption 2 and
maximal stable equilibria `d*_i` whose prices `p*_i = p_i(d*_i)` are strictly increasing, strictly
decreasing, or neither monotone nor antitone (the last forces `I ≥ 3`). -/
theorem proposition_1_pure_hv_equilibrium :
    (∀ (M : Market), 0 < M.a → 0 ≤ M.r → M.r < 1 → 0 < M.t2 → 0 < M.V → 0 < M.w0 → 0 ≤ M.α →
      ∀ {I : ℕ} (m : Fin I → ℝ), StrictMono m → (∀ i, 0 < m i) →
        (∀ i, IsLooseMarket M (m i)) →
        ∃ dstar : Fin I → ℝ,
          (∀ i, IsMaxStableHVEquilibrium M (m i) (dstar i) ∧
            ∀ d, IsMaxStableHVEquilibrium M (m i) d → d = dstar i) ∧
          (∀ i, revenue M (m i) (dstar i) =
              wage M (minSupply M (dstar i)) * minSupply M (dstar i) ∧
            minSupply M (dstar i) = aTilde M * dstar i ^ (1 / (M.r + 1)) + M.t2 * dstar i) ∧
          StrictMono dstar ∧
          (0 < M.r → StrictMono (fun i => util M (dstar i))) ∧
          (M.r = 0 → ∀ i j, util M (dstar i) = util M (dstar j)) ∧
          StrictMono (fun i => minSupply M (dstar i)) ∧
          (∀ i, invDemand M (m i) (dstar i) =
            wage M (minSupply M (dstar i)) / util M (dstar i))) ∧
    (∃ (M : Market) (I : ℕ) (m : Fin I → ℝ) (dstar : Fin I → ℝ),
        0 < M.a ∧ 0 ≤ M.r ∧ M.r < 1 ∧ 0 < M.t2 ∧ 0 < M.V ∧ 0 < M.w0 ∧ 0 ≤ M.α ∧
        2 ≤ I ∧ StrictMono m ∧ (∀ i, 0 < m i) ∧ (∀ i, IsLooseMarket M (m i)) ∧
        (∀ i, IsMaxStableHVEquilibrium M (m i) (dstar i)) ∧
        StrictMono (fun i => invDemand M (m i) (dstar i))) ∧
    (∃ (M : Market) (I : ℕ) (m : Fin I → ℝ) (dstar : Fin I → ℝ),
        0 < M.a ∧ 0 ≤ M.r ∧ M.r < 1 ∧ 0 < M.t2 ∧ 0 < M.V ∧ 0 < M.w0 ∧ 0 ≤ M.α ∧
        2 ≤ I ∧ StrictMono m ∧ (∀ i, 0 < m i) ∧ (∀ i, IsLooseMarket M (m i)) ∧
        (∀ i, IsMaxStableHVEquilibrium M (m i) (dstar i)) ∧
        StrictAnti (fun i => invDemand M (m i) (dstar i))) ∧
    (∃ (M : Market) (I : ℕ) (m : Fin I → ℝ) (dstar : Fin I → ℝ),
        0 < M.a ∧ 0 ≤ M.r ∧ M.r < 1 ∧ 0 < M.t2 ∧ 0 < M.V ∧ 0 < M.w0 ∧ 0 ≤ M.α ∧
        StrictMono m ∧ (∀ i, 0 < m i) ∧ (∀ i, IsLooseMarket M (m i)) ∧
        (∀ i, IsMaxStableHVEquilibrium M (m i) (dstar i)) ∧
        ¬ Monotone (fun i => invDemand M (m i) (dstar i)) ∧
        ¬ Antitone (fun i => invDemand M (m i) (dstar i))) := by sorry

end RideHailingAV.PureHV
