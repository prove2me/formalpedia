-- Prove2me | Theorems.Thm_SybilClinch_lemma_4_17
-- name    : SybilClinch.lemma_4_17
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:45:27.44531+00:00
-- url     : https://prove2.me/theorems/4baf9f5e-7fc9-4c11-8c04-a670483090a6
-- title:
--   Lemma 4.17 — outsider accounting between the merged and the Sybil run
-- statement:
--   Fix an admissible target-based mechanism and a physical sell-$Y$ bidder of true type $(V,Q)$ with $V\ge p_\star$, $Q\ge0$. In the merged run it submits the single identity $(V,Q)$; in the Sybil run a finite set $G$ of identities $(v_i,q_i)$ with $q_G=\sum_{i\in G}q_i\le Q$; the outside identities $N$, their reports and the target are the same in both runs (43). Fix a price $p\ge p_\star$ with $p<V$ at which the merged run continues, and let $\Phi_p(t)=\sum_{j\in N:v_j>p}\min\{q_j,t\}$. If the Sybil run also continues, then
--   $$Y^S_N-Y^M_N=\Phi_p(h^M)-\Phi_p(h^S),\qquad p\,(W^S_N-W^M_N)=\mathrm{GainGap}_N,\qquad \beta^M-\beta^S=Q-q_G+d^S_G\ge0,$$
--   where $\mathrm{GainGap}_N=\Gamma^S_N-\Gamma^M_N$, $\beta=Y+B$, and $d^S_G$ is the total Sybil budget cancelled so far (including budgets removed as ineligible at the initial price). If the Sybil run has ended, then
--   $$Y^S_N\ge Y^M_N,\qquad p\,(W^S_N-W^M_N)\ge\mathrm{GainGap}_N.$$
--
--   Differences from the source:
--   - reading: continuous evolution by the primitive conditions (16)–(18) on event-free open intervals, on which the clock and state paths are absolutely continuous → IsRun: the event procedure is applied at every clock price; off Clinch the continuous part of dx_i has no mass; a clincher stays at the water level on a right neighbourhood of every price while active; no absolute-continuity requirement on the paths; reason: event prices may accumulate (lumps of an admissible target can be dense) and, for an admissible AMM whose right marginal ask is flat on a fat Cantor set, the sole-survivor path X = Z(p) is continuous but not absolutely continuous, so a literal AC requirement would admit no run; on event-free intervals with AC paths the two formulations coincide
--   - reading: reported values (v_i, q_i) ∈ ℝ²≥0 in the one-sided analysis → values in WithTop ℝ with the hypothesis v_i ≠ ⊤ for every identity; reason: the paper states that its one-sided analysis allows only finite-value reports (p.28); infinite values are the subject of Lemma 6.2
--   - encoding: d^S_G, the total Sybil budget cancelled so far → Σ_{i∈G} (q_i − y_i(p) − b_i(p)); reason: every reported budget is spent, still effective, or cancelled; same quantity
-- source:
--   Zhang, Li, Shi, Zhang, Xia, Han, Sybil-Proofness of Generalized Adaptive Clinching and Implications for Blockchain Mechanism Design, arXiv:2610.36629 (held copy sha256 93c5d05b…), §4.6, Lemma 4.17, p.23 (PDF p.25); setup (43), p.21 (PDF p.23)

import Mathlib
import Definitions.Def_SybilClinch_IsRun
import Definitions.Def_SybilClinch_TargetMech_Admissible
import Definitions.Def_SybilClinch_OneSidedProfile_Valid
import Definitions.Def_SybilClinch_Run_gain
import Definitions.Def_SybilClinch_Run_wealth
import Definitions.Def_SybilClinch_Run_beta
import Definitions.Def_SybilClinch_outsiderPhi
import Definitions.Def_SybilClinch_Run_waterLevel

set_option autoImplicit false

open Filter Topology Set MeasureTheory

namespace SybilClinch

/-- Zhang, Li, Shi, Zhang, Xia, Han, *Sybil-Proofness of Generalized Adaptive Clinching and Implications for Blockchain Mechanism Design*, arXiv:2610.36629 (held copy sha256 93c5d05b…), §4.6, Lemma 4.17 (Outsider accounting), printed p.23 (PDF p.25), in the setup of §4.6,
(43), printed p.21 (PDF p.23).

A physical sell-`Y` bidder of true type `(V, Q)`, `V ≥ p⋆`, submits the single report `(V, Q)` as
identity `i₀` in the merged run, and a finite set `G` of identities `(vᵢ, qᵢ)` with
`q_G = Σ_{i∈G} qᵢ ≤ Q` in the Sybil run; the outsiders `N`, their reports and the target are the
same in both runs. Fix a price `p < V` at which the merged run continues. If the Sybil run also
continues, then
`Y^S_N − Y^M_N = Φ_p(h^M) − Φ_p(h^S)` (48), `p(W^S_N − W^M_N) = GainGap_N` (49), and
`β^M − β^S = Q − q_G + d^S_G ≥ 0` (50), where `d^S_G` is the total Sybil budget cancelled so far.
If the Sybil run has ended, then `Y^S_N ≥ Y^M_N` and `p(W^S_N − W^M_N) ≥ GainGap_N` (51). Here
`GainGap_N = Γ^S_N − Γ^M_N`.

**Formalization Note.** `d^S_G = Σ_{i∈G} (qᵢ − yᵢ − bᵢ)`: every reported budget is either spent,
still effective, or cancelled (including removal as ineligible at the initial price). Values are
finite, as in the paper's one-sided analysis. -/
theorem lemma_4_17 (M : TargetMech) (hM : M.Admissible) (N G : Finset ℕ) (i₀ : ℕ)
    (hi₀ : i₀ ∉ N) (hNG : Disjoint N G) (PM PS : OneSidedProfile)
    (hPM : PM.ids = insert i₀ N) (hPS : PS.ids = N ∪ G)
    (hNrep : ∀ j ∈ N, PM.v j = PS.v j ∧ PM.q j = PS.q j)
    (hvalM : PM.Valid) (hvalS : PS.Valid) (hfinM : ∀ i ∈ PM.ids, PM.v i ≠ ⊤)
    (hfinS : ∀ i ∈ PS.ids, PS.v i ≠ ⊤)
    (V Q : ℝ) (hV : M.pstar ≤ V) (hvi₀ : PM.v i₀ = (V : WithTop ℝ)) (hqi₀ : PM.q i₀ = Q)
    (hqG : ∑ i ∈ G, PS.q i ≤ Q) (RM RS : Run) (hRM : IsRun M PM RM) (hRS : IsRun M PS RS)
    (p : ℝ) (hp : M.pstar ≤ p) (hpV : p < V) (hpM : p < RM.pf) :
    (p < RS.pf →
      RS.payOf M N p - RM.payOf M N p =
          outsiderPhi PS N p (RM.waterLevel M PM p) - outsiderPhi PS N p (RS.waterLevel M PS p) ∧
        p * (RS.wealth M PS N p - RM.wealth M PM N p) = RS.gain M N p - RM.gain M N p ∧
        RM.beta M PM p - RS.beta M PS p =
          Q - ∑ i ∈ G, PS.q i + ∑ i ∈ G, (PS.q i - RS.pay M i p - RS.bud M PS i p) ∧
        0 ≤ Q - ∑ i ∈ G, PS.q i + ∑ i ∈ G, (PS.q i - RS.pay M i p - RS.bud M PS i p)) ∧
    (RS.pf ≤ p →
      RM.payOf M N p ≤ RS.payOf M N p ∧
        RS.gain M N p - RM.gain M N p ≤ p * (RS.wealth M PS N p - RM.wealth M PM N p)) := by sorry

end SybilClinch
