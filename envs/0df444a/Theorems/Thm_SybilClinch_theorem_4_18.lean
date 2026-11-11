-- Prove2me | Theorems.Thm_SybilClinch_theorem_4_18
-- name    : SybilClinch.theorem_4_18
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:44:21.415498+00:00
-- url     : https://prove2.me/theorems/ab61a60d-c8a5-46b7-a695-bc7405056833
-- title:
--   Theorem 4.18 — Sybil-proofness of every admissible target-based clinching mechanism
-- statement:
--   In any admissible abstract target-based mechanism (capacity possibly $+\infty$), let a physical sell-$Y$ bidder have true type $(V,Q)$ with $V\ge p_\star$ and $Q\ge0$. In the merged run it submits the single identity $(V,Q)$; in the Sybil run it submits a finite set $G$ of sell-$Y$ identities with arbitrary finite nonnegative values $v_i$ and budgets with $q_G=\sum_{i\in G}q_i\le Q$; the outside identities, their reports and the target are identical in the two runs. Then truthful participation as the merged identity weakly dominates:
--   $$V X^M_G-Y^M_G\ \ge\ V X^S_G-Y^S_G,\qquad(52)$$
--   for every completed merged run and every completed Sybil run.
--
--   This is the paper's general Sybil-proofness result; with constant targets it gives the Sybil-proofness of the classical adaptive clinching auction.
--
--   Differences from the source:
--   - reading: continuous evolution by the primitive conditions (16)–(18) on event-free open intervals, on which the clock and state paths are absolutely continuous → IsRun: the event procedure is applied at every clock price; off Clinch the continuous part of dx_i has no mass; a clincher stays at the water level on a right neighbourhood of every price while active; no absolute-continuity requirement on the paths; reason: event prices may accumulate (lumps of an admissible target can be dense) and, for an admissible AMM whose right marginal ask is flat on a fat Cantor set, the sole-survivor path X = Z(p) is continuous but not absolutely continuous, so a literal AC requirement would admit no run; on event-free intervals with AC paths the two formulations coincide
--   - reading: reported values (v_i, q_i) ∈ ℝ²≥0 in the one-sided analysis → values in WithTop ℝ with the hypothesis v_i ≠ ⊤ for every identity; reason: the paper states that its one-sided analysis allows only finite-value reports (p.28); infinite values are the subject of Lemma 6.2
-- source:
--   Zhang, Li, Shi, Zhang, Xia, Han, Sybil-Proofness of Generalized Adaptive Clinching and Implications for Blockchain Mechanism Design, arXiv:2610.36629 (held copy sha256 93c5d05b…), §4.6, Theorem 4.18, p.23 (PDF p.25); setup (43), p.21 (PDF p.23)

import Mathlib
import Definitions.Def_SybilClinch_IsRun
import Definitions.Def_SybilClinch_TargetMech_Admissible
import Definitions.Def_SybilClinch_OneSidedProfile_Valid
import Definitions.Def_SybilClinch_Run_alloc
import Definitions.Def_SybilClinch_Run_payOf

set_option autoImplicit false

open Filter Topology Set MeasureTheory

namespace SybilClinch

/-- Zhang, Li, Shi, Zhang, Xia, Han, *Sybil-Proofness of Generalized Adaptive Clinching and Implications for Blockchain Mechanism Design*, arXiv:2610.36629 (held copy sha256 93c5d05b…), §4.6, Theorem 4.18 (Sybil-proofness for an admissible target-based mechanism), printed
p.23 (PDF p.25), in the setup of §4.6, (43), printed p.21 (PDF p.23).

In any admissible abstract target-based mechanism (capacity possibly `+∞`), let a physical
sell-`Y` bidder have true type `(V, Q)` with `V ≥ p⋆`. In the merged run it submits the single
report `(V, Q)` (identity `i₀`); in the Sybil run it submits a finite set `G` of sell-`Y`
identities with arbitrary values and `q_G = Σ_{i∈G} qᵢ ≤ Q`; outsiders `N`, their reports and the
target are identical. Then truthful merged participation weakly dominates:
`V·X^M_G − Y^M_G ≥ V·X^S_G − Y^S_G` (52), for every completed merged run and every completed Sybil
run.

**Formalization Note.** Sybil values are arbitrary finite nonnegative numbers (also above `V` or
below `p⋆`); values are finite as in the paper's one-sided analysis. -/
theorem theorem_4_18 (M : TargetMech) (hM : M.Admissible) (N G : Finset ℕ) (i₀ : ℕ)
    (hi₀ : i₀ ∉ N) (hNG : Disjoint N G) (PM PS : OneSidedProfile)
    (hPM : PM.ids = insert i₀ N) (hPS : PS.ids = N ∪ G)
    (hNrep : ∀ j ∈ N, PM.v j = PS.v j ∧ PM.q j = PS.q j)
    (hvalM : PM.Valid) (hvalS : PS.Valid) (hfinM : ∀ i ∈ PM.ids, PM.v i ≠ ⊤)
    (hfinS : ∀ i ∈ PS.ids, PS.v i ≠ ⊤)
    (V Q : ℝ) (hV : M.pstar ≤ V) (hvi₀ : PM.v i₀ = (V : WithTop ℝ)) (hqi₀ : PM.q i₀ = Q)
    (hqG : ∑ i ∈ G, PS.q i ≤ Q) (RM RS : Run) (hRM : IsRun M PM RM) (hRS : IsRun M PS RS) :
    V * RS.alloc G RS.pf - RS.payOf M G RS.pf ≤ V * RM.x i₀ RM.pf - RM.pay M i₀ RM.pf := by sorry

end SybilClinch
