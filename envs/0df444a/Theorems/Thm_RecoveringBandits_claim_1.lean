-- Prove2me | Theorems.Thm_RecoveringBandits_claim_1
-- name    : RecoveringBandits.claim_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T07:54:26.791063+00:00
-- url     : https://prove2.me/theorems/73d4a59b-bbc6-4deb-bf2b-78a2fff406c4
-- title:
--   Claim 1 (proof of Lemma 1): an optimal schedule for $R^{cc}_i$ ends at $T$ and uses two consecutive gap lengths (corrected: $xT\ge1$)
-- statement:
--   Let arm $i$ be admissible, let $R^{cc}_i$ be its upper concave envelope, and consider problem (EC.1): maximize $\frac1T\sum_{j=1}^J R^{cc}_i(s_j-s_{j-1})$ over $J\le xT$ and $0=s_0<s_1<\dots<s_J\le T$. If $T\ge1$, $x\in[0,1]$ and $xT\ge1$, then (EC.1) has an optimal solution with
--
--   $$s_J=T\qquad\text{and}\qquad s_j-s_{j-1}\in\{d',d'+1\}\ \text{ for all } j,$$
--
--   for some integer $d'\ge1$.
--
--   This is the exchange step in the computation of the long-run value $F_i$: optimal schedules for a concave reward spread their pulls as evenly as possible.
--
--   Differences from the source:
--   - correction: Claim 1 for every T ≥ 1 and x ∈ [0,1] → adds the hypothesis x·T ≥ 1; reason: for x = 0, T = 1 the only feasible schedule has J = 0 and s_J = s_0 = 0 ≠ T; with x·T ≥ 1 an optimal schedule with J ≥ 1 exists since R^cc ≥ 0
--   - generalization: {s_j − s_{j−1}} takes at most two different values → all gaps lie in {d′, d′ + 1} for one d′ ≥ 1; reason: two consecutive values are at most two values; the proof's dist = 0 gives this and Claim 2 uses it
--   - encoding: a schedule s_1 < ⋯ < s_J and optimality for the objective (1/T)·Σ → the finite set S of pull times; optimality compares Σ without the factor 1/T against every feasible S′; reason: 1/T > 0 does not change the maximizers; same instances
-- source:
--   Simchi-Levi–Zheng–Zhu, Offline Planning and Online Learning under Recovering Rewards, arXiv:2106.14813v2, proof of Lemma 1, Claim 1, p.ec2 (PDF p.34)

import Mathlib
import Definitions.Def_RecoveringBandits_Admissible
import Definitions.Def_RecoveringBandits_schedReward
import Definitions.Def_RecoveringBandits_Rcc

namespace RecoveringBandits

/-- **Claim 1 (proof of Lemma 1)**, Simchi-Levi–Zheng–Zhu, arXiv:2106.14813v2, proof of Lemma 1,
Claim 1, p.ec2 (PDF p.34): for `T ≥ 1` and `x ∈ [0, 1]` with `x·T ≥ 1`, problem (EC.1) (problem
(2) with `R_i` replaced by its concave envelope `R^cc_i`) has an optimal solution that ends at
`s_J = T` and whose gaps `s_j − s_{j−1}` all lie in `{d′, d′ + 1}` for one `d′ ≥ 1`.

**Formalization Note.** A schedule is the finite set `S ⊆ [1, T]` of its pull times, `J = #S`;
"optimal" is stated by comparison with every feasible `S′`. Correction: the hypothesis `x·T ≥ 1`
is added (for `x = 0`, `T = 1` the only feasible schedule has `J = 0` and `s_J = s_0 = 0 ≠ T`).
Generalization: the two gap values are consecutive, which the proof's `dist = 0` gives and Claim 2
uses. -/
theorem claim_1 (r : ℕ → ℝ) (Rmax : ℝ) (hr : ArmAdmissible r Rmax) (T : ℕ) (hT : 1 ≤ T)
    (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hxT : 1 ≤ x * T) :
    ∃ S : Finset ℕ, S ⊆ Finset.Icc 1 T ∧ (S.card : ℝ) ≤ x * T ∧
      (∀ S' : Finset ℕ, S' ⊆ Finset.Icc 1 T → (S'.card : ℝ) ≤ x * T →
        schedReward (Rcc r) S' ≤ schedReward (Rcc r) S) ∧
      T ∈ S ∧
      ∃ d' : ℕ, 1 ≤ d' ∧ ∀ s ∈ S, s - prevPull S s = d' ∨ s - prevPull S s = d' + 1 := by sorry

end RecoveringBandits
