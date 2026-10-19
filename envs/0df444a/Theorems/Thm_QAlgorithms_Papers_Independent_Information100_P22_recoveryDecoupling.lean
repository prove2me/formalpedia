-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P22_recoveryDecoupling
-- name    : QAlgorithms.Papers.Independent.Information100.P22.recoveryDecoupling
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T10:01:26.214622+00:00
-- url     : https://prove2.me/theorems/4a89fdfb-0015-4605-9180-baf62262f270
-- title:
--   Lemma S1: Recovery–decoupling equivalence
-- statement:
--   Let $m,k\ge1$, $R$ be normalized and pure, and $U$ any AS unitary leaving $N$ untouched. For any fixed output $i$, let $E_i=A\bar S_i$ and form the normalized encoded Choi density $\Omega$. Then
--   $$\exists D_i\text{ CPTP}:D_iQ_i=\mathrm{id}\iff I(\widetilde A:E_i)_\Omega=0\iff\Omega_{\widetilde AE_i}=I_{\widetilde A}/2^k\otimes\Omega_{E_i}.$$
--   Mutual information uses base-two entropies. Channel equality includes arbitrary external correlations. This is the recovery–decoupling interface used by the paper.
-- source:
--   Beyond Maximal Entanglement : Exact Resources for Multiparty Encrypted Quantum Cloning, arXiv:2609.28241v1, PDF p. 19, Lemma S1: Recovery–decoupling equivalence

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P22

namespace QAlgorithms.Papers.Independent.Information100.P22

open scoped ComplexConjugate ComplexOrder Matrix

noncomputable section

local instance (p : Prop) : Decidable p := Classical.propDecidable p

/-- Lemma S1, PDF p.19: both recovery–decoupling equivalences. -/
theorem recoveryDecoupling (m k : ℕ) (hm : 1 ≤ m) (hk : 1 ≤ k)
    (R : EuclideanSpace ℂ (Signals m k × Signals m k)) (hR : IsState R)
    (U : Matrix.unitaryGroup (Qubits k × Signals m k) ℂ) (i : Fin m) :
    (Recoverable R (U : Op _) i ↔ quantumMI (referenceComplement R (U : Op _) i) = 0) ∧
    (Recoverable R (U : Op _) i ↔ referenceComplement R (U : Op _) i =
      Matrix.kronecker (mixed (Qubits k)) (traceLeft (referenceComplement R (U : Op _) i))) := by sorry

end

end QAlgorithms.Papers.Independent.Information100.P22
