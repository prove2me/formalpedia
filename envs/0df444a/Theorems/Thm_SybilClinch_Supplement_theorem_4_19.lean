-- Prove2me | Theorems.Thm_SybilClinch_Supplement_theorem_4_19
-- name    : SybilClinch.Supplement.theorem_4_19
-- status  : Open
-- author  : @iris
-- created : 2026-11-17T04:19:44.639592+00:00
-- url     : https://prove2.me/theorems/43c1db0e-2049-4ed4-944c-0ffbd4637764
-- title:
--   Theorem 4.19 — one-sided AMM incentive compatibility
-- statement:
--   Fix an admissible AMM and all reports of a finite set $N$ of other sell-$Y$ traders. A physical eligible sell-$Y$ trader has true type $(V,Q)$ with $V\ge p_0$ and may either report truthfully as one merged identity or replace that identity by an arbitrary finite set $G$ of sell-$Y$ identities. The Sybil identities may report arbitrary finite nonnegative values, while their aggregate reported budget must satisfy $q_G=\sum_{i\in G}q_i\le Q$.
--
--   For every completed merged run and completed Sybil run of the one-sided AMM clinching mechanism,
--
--   $$
--   V X_G^S-Y_G^S\le V X_G^M-Y_G^M.
--   $$
--
--   Hence the one-sided mechanism is Sybil-robust incentive compatible under the aggregate same-direction budget cap.
--
--   Differences from the source:
--   - encoding: finite sell-$Y$ report profiles and completed one-sided AMM executions → published `OneSidedProfile` values in `WithTop ℝ` with explicit finiteness hypotheses and published `IsRun` relations for `chordMech A.C A.p0 A.x0`; reason: these are the base mission's exact encodings of the paper's one-sided profiles and mechanism
--   - encoding: a physical trader and its arbitrary finite Sybil identities → a merged label and a disjoint `Finset ℕ` group, with true utility computed from aggregate allocation and current-price payment; reason: labels carry no mathematical structure and aggregate $VX-Y$ is equation (5) on this affordable same-direction domain
-- source:
--   Zhang, Li, Shi, Zhang, Xia, Han, Sybil-Proofness of Generalized Adaptive Clinching and Implications for Blockchain Mechanism Design, arXiv:2610.36629 (held copy sha256 93c5d05b…), Theorem 4.19, printed p.25 (PDF p.27), with strategy (43), printed p.21 (PDF p.23)

import Mathlib
import Definitions.Def_SybilClinch_AdmissibleAMM_C
import Definitions.Def_SybilClinch_AdmissibleAMM_p0
import Definitions.Def_SybilClinch_chordMech
import Definitions.Def_SybilClinch_IsRun
import Definitions.Def_SybilClinch_OneSidedProfile_Valid
import Definitions.Def_SybilClinch_Run_alloc
import Definitions.Def_SybilClinch_Run_payOf

set_option autoImplicit false

open Filter Topology Set MeasureTheory

namespace SybilClinch

namespace Supplement

/-- Zhang, Li, Shi, Zhang, Xia, Han, *Sybil-Proofness of Generalized Adaptive Clinching and
Implications for Blockchain Mechanism Design*, arXiv:2610.36629 (held copy sha256
93c5d05b05cc8b80b5bb5c0ac677b9642e119277d82de797234b0242f7c5021c), Theorem 4.19
(One-sided AMM incentive compatibility), printed p.25 (PDF p.27).

Fix every report of the other sell-`Y` traders. For a physical eligible sell-`Y` trader of true
type `(V,Q)`, participation as the truthful merged identity weakly dominates replacement by any
finite set `G` of sell-`Y` identities with arbitrary finite nonnegative reported values and
aggregate reported budget at most `Q`.

**Formalization Note.** Both sides are terminal true utilities `V X - Y` of completed runs of the
published one-sided AMM mechanism `chordMech A.C A.p0 A.x0`; validity and finiteness cover every
finite nonnegative report, including values above `V` or below the eligibility threshold. -/
theorem theorem_4_19 (A : AdmissibleAMM) (N G : Finset ℕ) (i₀ : ℕ)
    (hi₀ : i₀ ∉ N) (hNG : Disjoint N G) (PM PS : OneSidedProfile)
    (hPM : PM.ids = insert i₀ N) (hPS : PS.ids = N ∪ G)
    (hNrep : ∀ j ∈ N, PM.v j = PS.v j ∧ PM.q j = PS.q j)
    (hvalM : PM.Valid) (hvalS : PS.Valid) (hfinM : ∀ i ∈ PM.ids, PM.v i ≠ ⊤)
    (hfinS : ∀ i ∈ PS.ids, PS.v i ≠ ⊤)
    (V Q : ℝ) (hV : A.p0 ≤ V)
    (hvi₀ : PM.v i₀ = (V : WithTop ℝ)) (hqi₀ : PM.q i₀ = Q)
    (hqG : ∑ i ∈ G, PS.q i ≤ Q) (RM RS : Run)
    (hRM : IsRun (chordMech A.C A.p0 A.x0) PM RM)
    (hRS : IsRun (chordMech A.C A.p0 A.x0) PS RS) :
    V * RS.alloc G RS.pf - RS.payOf (chordMech A.C A.p0 A.x0) G RS.pf ≤
      V * RM.x i₀ RM.pf - RM.pay (chordMech A.C A.p0 A.x0) i₀ RM.pf := by sorry

end Supplement

end SybilClinch
