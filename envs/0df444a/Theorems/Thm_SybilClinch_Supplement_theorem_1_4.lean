-- Prove2me | Theorems.Thm_SybilClinch_Supplement_theorem_1_4
-- name    : SybilClinch.Supplement.theorem_1_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-17T04:17:52.285017+00:00
-- url     : https://prove2.me/theorems/9204e134-f1a2-48c9-942f-972e9e67039a
-- title:
--   Theorem 1.4 — Sybil-proofness with exogenous online supply
-- statement:
--   Fix before bidding an exogenous nondecreasing path of cumulative supplies
--
--   $$
--   0=s_0\le s_1\le\cdots\le s_m,
--   $$
--
--   together with the identities, their reports and budgets. At each step $t$, online adaptive clinching runs a fresh classical zero-start auction to completion with fixed supply $s_t$; its terminal allocation and payment are the cumulative outcome announced at that step.
--
--   Compare truthful participation by a physical bidder of type $(V,Q)$ as one merged identity with any finite same-direction Sybil split having arbitrary finite nonnegative value reports and aggregate declared budget at most $Q$, while all outside reports and the realized supply path remain fixed. At every step with $s_t>0$, their cumulative utilities satisfy
--
--   $$
--   u_t^S\le u_t^M.
--   $$
--
--   Differences from the source:
--   - encoding: a finite exogenous online supply path fixed independently of reports → one monotone function `supply : Fin (m+1) → ℝ`, fixed before and shared by the merged and Sybil profiles; reason: sharing the same function is the deterministic formalization of report-independent exogeneity for a fixed realized path
--   - encoding: at step $t$ the clock is run afresh from zero against constant target $s_t$ → a separate `zeroStartUtility (supply t)` relation at each positive-supply step; reason: Appendix B.2 distinguishes the online step from clock time and Corollary B.8 applies pointwise to every prefix
--   - encoding: finitely many auction identities → `Finset ℕ` labels with report functions and disjoint outside/Sybil sets; reason: labels carry no mathematical structure and this is the published mission convention
-- source:
--   Zhang, Li, Shi, Zhang, Xia, Han, Sybil-Proofness of Generalized Adaptive Clinching and Implications for Blockchain Mechanism Design, arXiv:2610.36629 (held copy sha256 93c5d05b…), Theorem 1.4, printed p.4 (PDF p.6), with Appendix B.2–B.3, printed pp.48–49 (PDF pp.50–51)

import Mathlib
import Definitions.Def_SybilClinch_OneSidedProfile_Valid
import Definitions.Def_SybilClinch_Supplement_zeroStartUtility

set_option autoImplicit false

open Filter Topology Set MeasureTheory

namespace SybilClinch

namespace Supplement

/-- Zhang, Li, Shi, Zhang, Xia, Han, *Sybil-Proofness of Generalized Adaptive Clinching and
Implications for Blockchain Mechanism Design*, arXiv:2610.36629 (held copy sha256
93c5d05b05cc8b80b5bb5c0ac677b9642e119277d82de797234b0242f7c5021c), Theorem 1.4
(Sybil-proofness with exogenous online supply), printed p.4 (PDF p.6), with Appendix B.2–B.3,
printed pp.48–49 (PDF pp.50–51).

Fix an exogenous nondecreasing cumulative supply path `0 = s₀ ≤ ⋯ ≤ sₘ`, identities,
reports and budgets before the first step. At every step `t` with positive cumulative supply, the
auction is run afresh from clock price zero for supply `s t`; truthful cumulative utility weakly
dominates the cumulative utility obtained by any finite same-direction Sybil split whose aggregate
reported budget is at most the true budget.

**Formalization Note.** Exogeneity is encoded by fixing one path before both profiles and using it
for both outcome families. `t` is distinct from the clock price: each `zeroStartUtility (supply t)`
comes from a fresh constant-target run, not from one clock with supply released along it. -/
theorem theorem_1_4 {m : ℕ} (supply : Fin (m + 1) → ℝ) (hs₀ : supply 0 = 0)
    (hsmono : Monotone supply) (N G : Finset ℕ) (i₀ : ℕ)
    (hi₀ : i₀ ∉ N) (hNG : Disjoint N G) (PM PS : OneSidedProfile)
    (hPM : PM.ids = insert i₀ N) (hPS : PS.ids = N ∪ G)
    (hNrep : ∀ j ∈ N, PM.v j = PS.v j ∧ PM.q j = PS.q j)
    (hvalM : PM.Valid) (hvalS : PS.Valid) (hfinM : ∀ i ∈ PM.ids, PM.v i ≠ ⊤)
    (hfinS : ∀ i ∈ PS.ids, PS.v i ≠ ⊤) (V Q : ℝ)
    (hvi₀ : PM.v i₀ = (V : WithTop ℝ)) (hqi₀ : PM.q i₀ = Q)
    (hqG : ∑ i ∈ G, PS.q i ≤ Q) (uM uS : Fin (m + 1) → ℝ)
    (huM : ∀ t, 0 < supply t → zeroStartUtility (supply t) PM {i₀} V (uM t))
    (huS : ∀ t, 0 < supply t → zeroStartUtility (supply t) PS G V (uS t)) :
    ∀ t, 0 < supply t → uS t ≤ uM t := by sorry

end Supplement

end SybilClinch
