-- Prove2me | Theorems.Thm_SybilClinch_Supplement_theorem_1_3
-- name    : SybilClinch.Supplement.theorem_1_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-17T04:17:14.893223+00:00
-- url     : https://prove2.me/theorems/47a3bc15-fa1c-48da-9a3b-b5c60dcb1d4a
-- title:
--   Theorem 1.3 — Sybil-proofness of fixed-supply adaptive clinching
-- statement:
--   Fix a divisible supply $s>0$, a finite set $N$ of outside identities, and a physical bidder with finite nonnegative true value and budget $(V,Q)$. Compare two profiles with the same reports for every identity in $N$:
--
--   1. the bidder participates truthfully as one merged identity reporting $(V,Q)$;
--   2. the bidder replaces that identity by an arbitrary finite set $G$ of identities with arbitrary finite nonnegative reported values and aggregate declared budget $q_G=\sum_{i\in G}q_i\le Q$.
--
--   If $u^M$ and $u^S$ are the bidder's utilities in the corresponding classical zero-start adaptive clinching outcomes, then
--
--   $$
--   u^S\le u^M.
--   $$
--
--   Thus truthful participation as one identity weakly dominates every same-direction finite Sybil split under the aggregate budget cap, including profiles with tied stopping exits.
--
--   Differences from the source:
--   - encoding: the classical clock starts at zero and the outcome includes the paper's singleton boundary convention → `zeroStartUtility`, the right limit of terminal utilities in constant-target runs as the positive start price tends to zero; reason: Lemma B.4 and Corollary B.8 identify these outcomes profile by profile, including the singleton limit, while `IsRun` encodes the simultaneous proportional rule at tied stopping exits
--   - encoding: finitely many auction identities → `Finset ℕ` labels with report functions and disjoint outside/Sybil sets; reason: labels carry no mathematical structure and this is the published mission convention
-- source:
--   Zhang, Li, Shi, Zhang, Xia, Han, Sybil-Proofness of Generalized Adaptive Clinching and Implications for Blockchain Mechanism Design, arXiv:2610.36629 (held copy sha256 93c5d05b…), Theorem 1.3, printed p.4 (PDF p.6), with Appendix B.1–B.3, printed pp.44–49 (PDF pp.46–51)

import Mathlib
import Definitions.Def_SybilClinch_OneSidedProfile_Valid
import Definitions.Def_SybilClinch_Supplement_zeroStartUtility

set_option autoImplicit false

open Filter Topology Set MeasureTheory

namespace SybilClinch

namespace Supplement

/-- Zhang, Li, Shi, Zhang, Xia, Han, *Sybil-Proofness of Generalized Adaptive Clinching and
Implications for Blockchain Mechanism Design*, arXiv:2610.36629 (held copy sha256
93c5d05b05cc8b80b5bb5c0ac677b9642e119277d82de797234b0242f7c5021c), Theorem 1.3
(Sybil-proofness of fixed-supply adaptive clinching), printed p.4 (PDF p.6), with Appendix B.1–B.3,
printed pp.44–49 (PDF pp.46–51).

For every fixed divisible supply `s > 0`, truthful participation by a bidder of true type `(V,Q)`
as one merged identity weakly dominates replacing it by any finite set `G` of identities with
arbitrary finite nonnegative values and aggregate reported budget at most `Q`, with every outside
identity and report fixed.

**Formalization Note.** Classical zero-start outcomes are `zeroStartUtility`: right limits of the
paper's constant-target runs. This includes the singleton boundary outcome and uses the paper's
simultaneous proportional rule at tied stopping exits. -/
theorem theorem_1_3 (s : ℝ) (hs : 0 < s) (N G : Finset ℕ) (i₀ : ℕ)
    (hi₀ : i₀ ∉ N) (hNG : Disjoint N G) (PM PS : OneSidedProfile)
    (hPM : PM.ids = insert i₀ N) (hPS : PS.ids = N ∪ G)
    (hNrep : ∀ j ∈ N, PM.v j = PS.v j ∧ PM.q j = PS.q j)
    (hvalM : PM.Valid) (hvalS : PS.Valid) (hfinM : ∀ i ∈ PM.ids, PM.v i ≠ ⊤)
    (hfinS : ∀ i ∈ PS.ids, PS.v i ≠ ⊤) (V Q : ℝ)
    (hvi₀ : PM.v i₀ = (V : WithTop ℝ)) (hqi₀ : PM.q i₀ = Q)
    (hqG : ∑ i ∈ G, PS.q i ≤ Q) (uM uS : ℝ)
    (huM : zeroStartUtility s PM {i₀} V uM)
    (huS : zeroStartUtility s PS G V uS) :
    uS ≤ uM := by sorry

end Supplement

end SybilClinch
