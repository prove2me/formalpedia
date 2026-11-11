-- Prove2me | Theorems.Thm_SybilClinch_lemma_6_4
-- name    : SybilClinch.lemma_6_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:47:32.077587+00:00
-- url     : https://prove2.me/theorems/1df8c7c3-e72b-4ab1-9563-2cda3b7bfdb5
-- title:
--   Lemma 6.4 — guaranteed allocation at the spot price
-- statement:
--   Let $\varphi$ be an admissible AMM, consider a profile of finite nonnegative reports in which sell-$Y$ is dominant ($D_Y\ge D_X$, $M=D_X$), let $\eta=D_Y-M$, and consider any completed run of the dominant auction on $\widetilde C_M$. At the initial price $p_0$ the residual supply is the initial target
--   $$S=\widetilde T_M(p_0,0,0)=M+Z(p_0),$$
--   and, before processing any identities that exit at $p_0$, the water level is
--   $$h_0=p_0D_Y-p_0\bigl(M+Z(p_0)\bigr)=p_0\bigl(\eta-Z(p_0)\bigr)\le p_0\eta.\qquad(61)$$
--   Every eligible dominant identity receives at least $x_i(p_0)\ge(q_i/p_0-\eta)_+$ at the spot price. Consequently a truthful identity $(V,Q)$, $V\ge p_0$, obtains utility at least $(V-p_0)(Q/p_0-\eta)_+$.
--
--   Differences from the source:
--   - reading: continuous evolution by the primitive conditions (16)–(18) on event-free open intervals, on which the clock and state paths are absolutely continuous → IsRun: the event procedure is applied at every clock price; off Clinch the continuous part of dx_i has no mass; a clincher stays at the water level on a right neighbourhood of every price while active; no absolute-continuity requirement on the paths; reason: event prices may accumulate (lumps of an admissible target can be dense) and, for an admissible AMM whose right marginal ask is flat on a fat Cantor set, the sole-survivor path X = Z(p) is continuous but not absolutely continuous, so a literal AC requirement would admit no run; on event-free intervals with AC paths the two formulations coincide
--   - encoding: p0 D_Y, the total dominant budget; a truthful identity (V, Q) → Σ_{i∈E_Y} q_i; every eligible dominant identity, its report (v_i, q_i) read as its type; reason: p0 D_Y = Σ_{E_Y} q_i by definition; the lemma's truthful identity is an arbitrary dominant identity
--   - encoding: the dominant auction's run → every completed run R of domYMech on domYProfile; reason: runs are relational
-- source:
--   Zhang, Li, Shi, Zhang, Xia, Han, Sybil-Proofness of Generalized Adaptive Clinching and Implications for Blockchain Mechanism Design, arXiv:2610.36629 (held copy sha256 93c5d05b…), §6.2, Lemma 6.4, p.29 (PDF p.31)

import Mathlib
import Definitions.Def_SybilClinch_TwoSidedOutcome
import Definitions.Def_SybilClinch_AdmissibleAMM_Zsupply
import Definitions.Def_SybilClinch_Report_Valid

set_option autoImplicit false

open Filter Topology Set MeasureTheory

namespace SybilClinch

/-- Zhang, Li, Shi, Zhang, Xia, Han, *Sybil-Proofness of Generalized Adaptive Clinching and Implications for Blockchain Mechanism Design*, arXiv:2610.36629 (held copy sha256 93c5d05b…), §6.2, Lemma 6.4 (Guaranteed allocation at the spot price), printed p.29 (PDF p.31).

Suppose sell-`Y` is dominant and let `η = D_Y − M`. At the initial price `p₀` the residual supply is
the initial target `S = T̃_M(p₀, 0, 0) = M + Z(p₀)`; before processing any identities that exit at
`p₀`, the water level is `h₀ = p₀D_Y − p₀(M + Z(p₀)) = p₀(η − Z(p₀)) ≤ p₀η` (61). Every eligible
dominant identity receives at least `xᵢ(p₀) ≥ (qᵢ/p₀ − η)₊`. Consequently a truthful identity
`(V, Q)`, `V ≥ p₀`, obtains utility at least `(V − p₀)(Q/p₀ − η)₊`.

**Formalization Note.** Stated for every completed run of the dominant auction. `p₀D_Y` is the total
dominant budget `Σ_{E_Y} qᵢ`; `xᵢ(p₀)` is the allocation after the events at `p₀`. The truthful
identity is any eligible dominant identity, its report `(vᵢ, qᵢ)` read as its type `(V, Q)`. -/
theorem lemma_6_4 (A : AdmissibleAMM) (ids : Finset ℕ) (rep : ℕ → Report)
    (hrep : ∀ i ∈ ids, (rep i).Valid) (hdom : demandX A ids rep ≤ demandY A ids rep)
    (R : Run) (hR : IsRun (domYMech A ids rep) (domYProfile A ids rep) R) :
    let Mf := demandX A ids rep
    let η := demandY A ids rep - Mf
    let h₀ := ∑ i ∈ eligY A ids rep, (rep i).bud -
      A.p0 * chordTarget (A.Ctil Mf) (Mf + A.x0) A.p0 0 0
    chordTarget (A.Ctil Mf) (Mf + A.x0) A.p0 0 0 = Mf + A.Zsupply A.p0 ∧
    h₀ = A.p0 * (η - A.Zsupply A.p0) ∧ h₀ ≤ A.p0 * η ∧
    (∀ i ∈ eligY A ids rep, max ((rep i).bud / A.p0 - η) 0 ≤ R.x i A.p0) ∧
    ∀ i ∈ eligY A ids rep,
      ((rep i).val - A.p0) * max ((rep i).bud / A.p0 - η) 0 ≤
        (rep i).val * R.x i R.pf - R.pay (domYMech A ids rep) i R.pf := by sorry

end SybilClinch
