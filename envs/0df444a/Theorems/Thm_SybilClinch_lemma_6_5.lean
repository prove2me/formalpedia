-- Prove2me | Theorems.Thm_SybilClinch_lemma_6_5
-- name    : SybilClinch.lemma_6_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:45:40.370616+00:00
-- url     : https://prove2.me/theorems/27c5e58a-5421-456f-a672-3ac944c61755
-- title:
--   Lemma 6.5 — fill-shift bound $U(M+E,Q+p_0E)\le U(M,Q)+(V-p_0)E$
-- statement:
--   Let $\varphi$ be an admissible AMM. Fix outside sell-$Y$ reports (a finite set $N$ of identities with finite nonnegative values and budgets) and a true value $V\ge p_0$. Let $U(M,Q)$ be the utility $Vx-y$ of the single truthful identity $(V,Q)$ in the one-sided run on $\widetilde C_M$ (no minority orders take part; the fill is a parameter of the cost). Then for all $M,E,Q\ge0$,
--   $$U(M+E,\,Q+p_0E)\le U(M,Q)+(V-p_0)E .$$
--   The extra $E$ units of initial supply, together with the $p_0E$ needed to buy them, raise the bidder's utility by no more than the surplus of buying them at the spot price.
--
--   Differences from the source:
--   - reading: continuous evolution by the primitive conditions (16)–(18) on event-free open intervals, on which the clock and state paths are absolutely continuous → IsRun: the event procedure is applied at every clock price; off Clinch the continuous part of dx_i has no mass; a clincher stays at the water level on a right neighbourhood of every price while active; no absolute-continuity requirement on the paths; reason: event prices may accumulate (lumps of an admissible target can be dense) and, for an admissible AMM whose right marginal ask is flat on a fat Cantor set, the sole-survivor path X = Z(p) is continuous but not absolutely continuous, so a literal AC requirement would admit no run; on event-free intervals with AC paths the two formulations coincide
--   - encoding: U(M, Q), the utility in the one-sided run on C̃_M → V·x_{i0} − y_{i0} in every completed run of each of the two profiles (focal label i0 ∉ N); reason: runs are relational; the inequality is required for every pair of runs
-- source:
--   Zhang, Li, Shi, Zhang, Xia, Han, Sybil-Proofness of Generalized Adaptive Clinching and Implications for Blockchain Mechanism Design, arXiv:2610.36629 (held copy sha256 93c5d05b…), §6.3, Lemma 6.5 and the definition of U above it, p.30 (PDF p.32)

import Mathlib
import Definitions.Def_SybilClinch_IsRun
import Definitions.Def_SybilClinch_chordMech
import Definitions.Def_SybilClinch_AdmissibleAMM_Ctil
import Definitions.Def_SybilClinch_OneSidedProfile

set_option autoImplicit false

open Filter Topology Set MeasureTheory

namespace SybilClinch

/-- Zhang, Li, Shi, Zhang, Xia, Han, *Sybil-Proofness of Generalized Adaptive Clinching and Implications for Blockchain Mechanism Design*, arXiv:2610.36629 (held copy sha256 93c5d05b…), §6.3, Lemma 6.5 (Fill-shift bound), printed p.30 (PDF p.32), with the definition of
`U(M, Q)` just above it.

Fix outside sell-`Y` reports and a true value `V ≥ p₀`. Let `U(M, Q)` be the utility of the single
truthful identity `(V, Q)` in the one-sided run on `C̃_M` (no minority orders take part). For all
`M, E, Q ≥ 0`, `U(M + E, Q + p₀E) ≤ U(M, Q) + (V − p₀)E`.

**Formalization Note.** The outsiders are a finite set `N` with finite nonnegative reports
`(vN, qN)`, the focal identity is a label `i₀ ∉ N`. With relational runs the inequality is stated for
every completed run of each of the two profiles. -/
theorem lemma_6_5 (A : AdmissibleAMM) (N : Finset ℕ) (i₀ : ℕ) (hi₀ : i₀ ∉ N)
    (vN : ℕ → WithTop ℝ) (qN : ℕ → ℝ) (hN : ∀ j ∈ N, 0 ≤ vN j ∧ vN j ≠ ⊤ ∧ 0 ≤ qN j)
    (V : ℝ) (hV : A.p0 ≤ V) (Mf E Q : ℝ) (hM : 0 ≤ Mf) (hE : 0 ≤ E) (hQ : 0 ≤ Q)
    (R₀ R₁ : Run)
    (hR₀ : IsRun (chordMech (A.Ctil Mf) A.p0 (Mf + A.x0))
      ⟨insert i₀ N, Function.update vN i₀ (V : WithTop ℝ), Function.update qN i₀ Q⟩ R₀)
    (hR₁ : IsRun (chordMech (A.Ctil (Mf + E)) A.p0 (Mf + E + A.x0))
      ⟨insert i₀ N, Function.update vN i₀ (V : WithTop ℝ),
        Function.update qN i₀ (Q + A.p0 * E)⟩ R₁) :
    V * R₁.x i₀ R₁.pf - R₁.pay (chordMech (A.Ctil (Mf + E)) A.p0 (Mf + E + A.x0)) i₀ R₁.pf ≤
      V * R₀.x i₀ R₀.pf - R₀.pay (chordMech (A.Ctil Mf) A.p0 (Mf + A.x0)) i₀ R₀.pf +
        (V - A.p0) * E := by sorry

end SybilClinch
