-- Prove2me | Theorems.Thm_StrategyProofArrow_Dictatorship_lemma_5
-- name    : StrategyProofArrow.Dictatorship.lemma_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:48:16.320859+00:00
-- url     : https://prove2.me/theorems/8dcf7e60-d284-489d-8cd8-75a89b4f9c91
-- title:
--   Lemma 5 — a strategy-proof strict voting procedure is fully dictatorial or strong alternative-excluding
-- statement:
--   Consider a strict committee $\langle I_n,S_m,v^{nm},T_p\rangle$ with $n\ge 1$, $m\ge 3$ and $p\ge 1$. If $v^{nm}$ is strategy-proof, then
--
--   $$v^{nm}\ \text{is fully dictatorial}\quad\text{or}\quad v^{nm}\ \text{is strong alternative-excluding.}$$
--
--   When the range is all of $S_m$ this is the classical Gibbard–Satterthwaite theorem; when the range is a proper subset, it asserts Condition U. The paper proves the case $m=3$ (Lemmas 2–4) and refers to its reference [13] for the induction on $m$.
--
--   **Formalization Note** The case $T_p=S_m$ is the published theorem `AGT.gibbard_satterthwaite` (an incentive compatible social choice function onto more than two alternatives has a voter whose unique top alternative is always elected), included in this mission as a reference item.
-- source:
--   Satterthwaite, Strategy-proofness and Arrow's Conditions, Northwestern Discussion Paper No. 122 (rev. Dec. 12, 1974), Lemma 5, p. 25

import Mathlib
import Definitions.Def_StrategyProofArrow_Dictatorship_Basic

namespace StrategyProofArrow.Dictatorship

open AGT

/-- **Lemma 5** (Satterthwaite, p. 25). For a strict committee with `n ≥ 1`, `m ≥ 3` and
`p ≥ 1`, a strategy-proof strict voting procedure is either fully dictatorial or strong
alternative-excluding. -/
theorem lemma_5 {ι A : Type*} [Fintype ι] [Fintype A] [DecidableEq ι]
    (hn : 1 ≤ Fintype.card ι) (hm : 3 ≤ Fintype.card A)
    (f : (ι → A → A → Prop) → A) (hp : 1 ≤ (range f).ncard)
    (hsp : IncentiveCompatible f) :
    FullyDictatorial f ∨ StrongAltExcluding f := by sorry

end StrategyProofArrow.Dictatorship
