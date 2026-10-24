-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P41_unitaryRepresentation
-- name    : QAlgorithms.Papers.Independent.Support50.P41.unitaryRepresentation
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T22:12:46.753552+00:00
-- url     : https://prove2.me/theorems/b368c9f6-9261-45da-aa2b-c7302fd0ecfa
-- title:
--   §2.2 theorem I; §A.3: pure-environment unitary representation
-- statement:
--   Let $\Phi:M_d(\mathbb C)\to M_d(\mathbb C)$ be complex linear, completely positive, and trace preserving, with $d\ge1$. There exist an environment of dimension $1\le e\le d^2$, a unit vector $\eta$, and a unitary $U$ on system and environment such that, for every matrix $X$,
--
--   $$\Phi(X)=\operatorname{Tr}_E[U(X\otimes|\eta\rangle\langle\eta|)U^\dagger].$$
--
--   This realizes the channel using a fixed initially independent pure environment.
-- source:
--   Sending quantum entanglement through noisy channels, arXiv:quant-ph/9604023v1, PDF p. 6, §2.2 theorem I; §A.3: pure-environment unitary representation

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P41

noncomputable section

namespace QAlgorithms.Papers.Independent.Support50.P41

open QAlgorithms

open QAlgorithms.Entanglement (IsCompletelyPositive)

open QAlgorithms.Papers.Independent.Dependency50.P40 (IsPurification purificationFidelity)

open QAlgorithms.Papers.Independent.Dependency50.P45 (entropyExchange)

open QAlgorithms.Papers.Independent.Information100.P08 (canonicalPurification)

open QAlgorithms.Papers.Independent.Information100.P34 (choi dephasing)

open QAlgorithms.Papers.Independent.Dependency50.P38 (vectorizeInputFirst)

open QAlgorithms.Papers.Independent.Gap20.P06 (dilationChannel environmentOutput dilatedVector)

open QAlgorithms.Papers.Independent.Information100.P50 (complementaryMap)

open QAlgorithms.Papers.Independent.Renew46.P43 (IsCountablePOVM classicalKLTerm countableEntropy)

open scoped Matrix ComplexConjugate ComplexOrder ENNReal

attribute [local instance] Classical.propDecidable Classical.decEq

-- The accepted generic dilation functions fix classical equality on each factor.
-- Match that instance for Fin before forming their product unitary groups.

local instance (priority := 2000) (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _

/-- PDF pp.5--6,35--36, theorem I: pure-environment unitary representation with dimension bound. -/
theorem unitaryRepresentation {d : ℕ} [NeZero d]
    (Phi : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ)
    (hCP : IsCompletelyPositive Phi) (hTP : ∀ X, (Phi X).trace = X.trace) :
    ∃ e : ℕ, 0 < e ∧ e ≤ d^2 ∧
      ∃ eta : EuclideanSpace ℂ (Fin e), IsState eta ∧
        ∃ U : Matrix.unitaryGroup (Fin d × Fin e) ℂ,
          ∀ X, Phi X = dilationChannel U eta X := by sorry

end QAlgorithms.Papers.Independent.Support50.P41

end
