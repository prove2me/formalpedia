-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P77_joint_sampling_deviation
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P77.joint_sampling_deviation
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T08:01:02.307123+00:00
-- url     : https://prove2.me/theorems/8f80d5f5-d8f4-47b4-b804-ca411219baf6
-- title:
--   Joint sampling deviation with boundary-inclusive information tail
-- statement:
--   Let $n\ge1$ and fix an arbitrary normalized probability law on binary error strings $C\in\{0,1\}^{2n}$, for a fixed basis. Independently choose a uniformly random $n$-element subset $S$ as the information positions; its complement is the test set. Let $C_I,C_T$ be the restrictions of $C$. For $0\le p_a\le1$ and $\epsilon>0$,
--
--   $$\Pr\bigl[|C_I|\ge n(p_a+\epsilon)\ \text{and}\ |C_T|\le np_a\bigr]\le2\exp(-n\epsilon^2/2).$$
--
--   This is a joint event, averaged over the balanced partition and the full error law, without conditioning on passing. The boundary-inclusive information endpoint follows the weak-tail bound in Appendix M, Eq. (41).
-- source:
--   A Proof of the Security of Quantum Key Distribution, arXiv:quant-ph/9912053v1, PDF p. 10, Lemma 4.4: joint sampling deviation

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P77

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakenext100.P77

open scoped BigOperators ComplexConjugate ComplexOrder

open QAlgorithms

-- The repair instruction authorizes imports of pinned accepted definitions.
-- These are definitions only; no imported paper theorem is used here.

open QAlgorithms.Papers.Independent.Dependency50.P47 (Law)

open QAlgorithms.Papers.Independent.Information100.P04 (Measurement)

open QAlgorithms.Papers.Independent.Information100.P27 (shannon)

open QAlgorithms.Papers.Independent.Information100.P39 (pushLaw)

open QAlgorithms.Papers.Independent.Support50.P16 (trivialMeasurement)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Lemma 4.4, PDF p.10; Appendices L--M, pp.27--28. SOURCE CORRECTION:
printed information event is strict '>'; changed to '>=' to retain Eq.(8)'s
boundary. Weak-tail Eq.(41) proves this boundary-inclusive bound with the same
constant. Test endpoint '<=' follows the protocol. Independent moderation needed. -/
theorem joint_sampling_deviation {n : ℕ} (hn : 1 ≤ n)
    (p : Law (Qubits (n + n))) (allowed margin : ℝ)
    (hp : 0 ≤ allowed) (hp1 : allowed ≤ 1) (he : 0 < margin) :
    samplingDeviation p allowed margin ≤ 2 * Real.exp (-(n : ℝ) * margin ^ 2 / 2) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P77

end
