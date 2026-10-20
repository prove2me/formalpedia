-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P48_keyDominatesGeneration
-- name    : QAlgorithms.Papers.Independent.Dependency50.P48.keyDominatesGeneration
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T15:43:23.041234+00:00
-- url     : https://prove2.me/theorems/98957b19-e516-40cb-8072-43c983aa3cba
-- title:
--   Secret-key capacity is at least entanglement-generation capacity
-- statement:
--   Let $\mathcal N$ be a finite-dimensional quantum channel with a fixed isometric dilation $P\to Q\otimes E$, where all registers are nonempty and Eve controls the full complement $E$. Let $E(\mathcal N)$ be its unassisted entanglement-generation capacity with squared fidelity to the normalized maximally entangled state, and let $K(\mathcal N)$ be its uniform-secret-key capacity with separate public and conditional Eve leakage constraints and free forward public communication. There are no initial shared resources or backward channels. With bit rates per use,
--
--   $$K(\mathcal N)\ge E(\mathcal N).$$
--
--   This operational comparison does not assert a strict inequality or identify either capacity with a diamond-error model.
-- source:
--   The private classical capacity and quantum capacity of a quantum channel, arXiv:quant-ph/0304127v6, PDF p. 11, Section 4 remark

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P48

noncomputable section

namespace QAlgorithms.Papers.Independent.Dependency50.P48

open scoped BigOperators Matrix ComplexConjugate

open Filter

open QAlgorithms.Papers.Independent.Information100.P22 (coherentInformation)

open QAlgorithms.Papers.Independent.Information100.P27 (shannon)

open QAlgorithms.Papers.Independent.Information100.P67 (dilationPower)

attribute [local instance] Classical.propDecidable

variable {P Q E X H : Type*}

variable [Fintype P] [DecidableEq P] [Fintype Q] [DecidableEq Q]

variable [Fintype E] [DecidableEq E] [Fintype X] [DecidableEq X]

variable [Fintype H] [DecidableEq H]

/-- Section 4 remark, PDF p.11, reiterated p.15: secret-key capacity is at
least entanglement-generation capacity. No strict capacity separation is claimed. -/
theorem keyDominatesGeneration [Nonempty P] [Nonempty Q] [Nonempty E]
    (U : Matrix (Q × E) P ℂ) (hU : IsDilation U) :
    generationCapacity U ≤ quantumPrivateCapacity U .key true := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P48

end
