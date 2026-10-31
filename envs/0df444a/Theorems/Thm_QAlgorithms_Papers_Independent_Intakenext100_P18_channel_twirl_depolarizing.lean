-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P18_channel_twirl_depolarizing
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P18.channel_twirl_depolarizing
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T04:25:43.949737+00:00
-- url     : https://prove2.me/theorems/618d8e26-01b6-4335-948e-70841701dd5a
-- title:
--   Channel twirling gives a depolarizing channel with the same entanglement fidelity
-- statement:
--   Let $d\ge1$ and let $\Lambda$ be any completely positive trace-preserving map on $d$-dimensional matrices. Put $F(\Lambda)=\operatorname{Tr}[P_+(\operatorname{id}\otimes\Lambda)(P_+)]$ for the fixed normalized plus Bell projector. With probability Haar measure on $U(d)$, define
--
--   $$\mathcal T(\Lambda)(X)=\int U^\dagger\Lambda(UXU^\dagger)U\,dU.$$
--
--   This is a channel and $F(\mathcal T(\Lambda))=F(\Lambda)$. If $d\ge2$, it equals the depolarizing map $D_p(X)=pX+(1-p)\operatorname{Tr}(X)I/d$, where
--
--   $$p=\frac{d^2F(\Lambda)-1}{d^2-1}\in\left[-\frac1{d^2-1},1\right].$$
--
--   At $d=1$ it is the identity channel, represented by $p=1$. This extends the preliminary convex-mixture parameter range as required by the lemma's every-channel quantifier. A traceless unitary channel can have $F=0$.
-- source:
--   General teleportation channel, singlet fraction and quasi-distillation, arXiv:quant-ph/9807091v2, PDF p. 6, §III.D, Lemma 1, eq.(21): channel twirling preserves entanglement fidelity

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P18

noncomputable section

open QAlgorithms MeasureTheory

open scoped Matrix ComplexConjugate ComplexOrder Matrix.Norms.L2Operator

namespace QAlgorithms.Papers.Independent.Intakenext100.P18

open QAlgorithms.Papers.Independent.Claimed50.P28 (maximallyEntangledDensity)

open QAlgorithms.Papers.Independent.Support50.P11 (choiState teleportWeyl bellKet)

open QAlgorithms.Papers.Independent.Renew46.P40 (initialJoint)

/-- PDF pp.6--7, Lemma 1, (21),(25). Source correction: arbitrary channels
require the full CP depolarizing retention range, including negative values.
Dimension one is split before division by d^2-1. -/
theorem channel_twirl_depolarizing (d : ℕ) (hd : 0 < d)
    (E : Superop (Fin d) (Fin d)) (hE : IsChannel E) :
    IsChannel (QuditFidelity.haarTwirl d hd E) ∧
    QuditFidelity.entanglementFidelity d hd (QuditFidelity.haarTwirl d hd E) =
      QuditFidelity.entanglementFidelity d hd E ∧
    (d = 1 → QuditFidelity.haarTwirl d hd E = retentionChannel d hd 1) ∧
    (2 ≤ d →
      let p := ((d : ℝ)^2 * QuditFidelity.entanglementFidelity d hd E - 1) / ((d : ℝ)^2 - 1);
      -(1 / ((d : ℝ)^2 - 1)) ≤ p ∧ p ≤ 1 ∧
      QuditFidelity.haarTwirl d hd E = retentionChannel d hd p) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P18

end
