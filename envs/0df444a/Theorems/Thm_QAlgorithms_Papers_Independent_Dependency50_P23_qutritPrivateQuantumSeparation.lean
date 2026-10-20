-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P23_qutritPrivateQuantumSeparation
-- name    : QAlgorithms.Papers.Independent.Dependency50.P23.qutritPrivateQuantumSeparation
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T16:47:35.107031+00:00
-- url     : https://prove2.me/theorems/e7e38e4d-8e14-446a-b406-ae29a99ec9d8
-- title:
--   Proposition 16: private capacity and quantum/private separation
-- statement:
--   Let $0<\alpha\le\pi/4$, and define $\mathcal N_\alpha$ using $E_0=\sin\alpha|0\rangle\langle1|+|1\rangle\langle2|$ and $E_1=\cos\alpha|2\rangle\langle1|+|1\rangle\langle0|$. Write $P,Q,C,C_E$ for ordinary private, quantum, classical and entanglement-assisted classical capacities. With the complementary environment fixed by these Kraus operators,
--
--   $$Q(\mathcal N_\alpha)\le\log_2(1+\cos\alpha)<1=P(\mathcal N_\alpha)=C(\mathcal N_\alpha)=\tfrac12 C_E(\mathcal N_\alpha).$$
--
--   No privacy of a proposed code is assumed. Quantum capacity uses general CPTP entanglement-transmission codes, and private capacity uses vanishing joint decoding/privacy error. This is the full displayed separation, including the factor one half.
-- source:
--   Semidefinite programming strong converse bounds for classical capacity, arXiv:1610.06381v4, PDF p. 19, Proposition 16

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P23

noncomputable section

namespace QAlgorithms.Papers.Independent.Dependency50.P23

open scoped Matrix ComplexConjugate ComplexOrder

open Filter

open QAlgorithms.Papers.Independent.Information100.P34 (choi)

open QAlgorithms.Papers.Independent.Information100.P08 (canonicalPurification)

open QAlgorithms.Papers.Independent.Information100.P62 (tensorChannel)

open QAlgorithms.Papers.Independent.Information100.P80 (log2 quantumCapacity)

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

variable {A B C D : Type} [Fintype A] [Fintype B] [Fintype C] [Fintype D]

variable [DecidableEq A] [DecidableEq B] [DecidableEq C] [DecidableEq D]

/-- PDF pp.19–20, Proposition 16: full quantum/private/classical/EA chain.
The displayed theorem gives Q≤log(1+cos alpha); the proof's stronger prose is
not substituted. Perfect privacy of the constructed code is not a hypothesis. -/
theorem qutritPrivateQuantumSeparation (alpha : ℝ)
    (ha0 : 0 < alpha) (ha1 : alpha ≤ Real.pi/4) :
    (QAlgorithms.Papers.Independent.Information100.P67.privateCapacity
      .uniformOptimized (qutritDilation alpha)) = 1 ∧
    quantumCapacity (qutrit alpha) ≤ log2 (1 + Real.cos alpha) ∧
    log2 (1 + Real.cos alpha) < 1 ∧
    ordinaryClassicalCapacity (qutrit alpha) = 1 ∧
    ordinaryClassicalCapacity (qutrit alpha) = (1/2 : ℝ) * eaCapacity (qutrit alpha) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P23

end
