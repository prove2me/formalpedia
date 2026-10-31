-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P18_depolarizing_teleportation
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P18.depolarizing_teleportation
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T04:24:49.151365+00:00
-- url     : https://prove2.me/theorems/62ca54a8-ba59-4702-b496-eb2fdbc10c49
-- title:
--   Standard teleportation realizes the depolarizing channel
-- statement:
--   Let $d\ge1$ and $0\le p\le1$. Define the noisy singlet $\rho_p=pP_++(1-p)I/d^2$ and the linear depolarizing map $D_p(X)=pX+(1-p)\operatorname{Tr}(X)I/d$. Let $J$ be the reference-first normalized Choi map and let $T_{0,\rho_p}$ be the channel computed by the complete Bell measurement with its outcome-conditioned Weyl correction, using one resource copy. Then $D_p$ is a channel and
--
--   $$J(D_p)=\rho_p,\qquad \Lambda_{\rho_p}=T_{0,\rho_p}=D_p.$$
--
--   The fixed plus overlap of $\rho_p$ equals the entanglement fidelity of $D_p$, and their standard-teleportation and channel Haar-average fidelities agree. This supplies the physical recovery that is special to this channel family.
--
--   **Formalization Note** The accepted depolarizing map uses noise weight, so the source retention parameter $p$ is supplied as $1-p$. Equality of maps ranges over every operator, including non-unit-trace operators.
-- source:
--   General teleportation channel, singlet fraction and quasi-distillation, arXiv:quant-ph/9807091v2, PDF p. 6, §III.C, eqs.(19)–(20): depolarizing channel recovered by standard teleportation

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P18

noncomputable section

open QAlgorithms MeasureTheory

open scoped Matrix ComplexConjugate ComplexOrder Matrix.Norms.L2Operator

namespace QAlgorithms.Papers.Independent.Intakenext100.P18

open QAlgorithms.Papers.Independent.Claimed50.P28 (maximallyEntangledDensity)

open QAlgorithms.Papers.Independent.Support50.P11 (choiState teleportWeyl bellKet)

open QAlgorithms.Papers.Independent.Renew46.P40 (initialJoint)

/-- PDF p.6, (19)--(20): depolarizing channels and noisy singlets are
mathematically and operationally equivalent through the actual Bell protocol. -/
theorem depolarizing_teleportation (d : ℕ) (hd : 0 < d) (p : ℝ)
    (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    IsChannel (retentionChannel d hd p) ∧
    choiState (retentionChannel d hd p) = noisySinglet d hd p ∧
    choiInverse d (noisySinglet d hd p) = retentionChannel d hd p ∧
    standardTeleport d (noisySinglet d hd p) = retentionChannel d hd p ∧
    QuditFidelity.entanglementFidelity d hd (retentionChannel d hd p) =
      effectProb (maximallyEntangledDensity d) (noisySinglet d hd p) ∧
    QuditFidelity.averageFidelity d hd (retentionChannel d hd p) =
      QuditFidelity.averageFidelity d hd (standardTeleport d (noisySinglet d hd p)) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P18

end
