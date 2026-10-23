-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P22_keyUnitaryClass
-- name    : QAlgorithms.Papers.Independent.Information100.P22.keyUnitaryClass
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T10:06:46.99267+00:00
-- url     : https://prove2.me/theorems/e72eb5e8-8a09-4b6c-9d37-72d2501b5bf4
-- title:
--   §II B, unnumbered: key-side unitary equivalence of maximally entangled resources
-- statement:
--   For $m,k\ge1$, let $R$ be normalized and pure with $\rho_S=I/2^{mk}$ and equally sized signal/key registers. There is a key-only unitary $V_N$ such that
--   $$|R\rangle=(I_S\otimes V_N)|\Phi_{2^{mk}}\rangle.$$
--   The equality includes any scalar phase in $V_N$. This identifies the entire maximally entangled resource class with one purification orbit.
-- source:
--   Beyond Maximal Entanglement : Exact Resources for Multiparty Encrypted Quantum Cloning, arXiv:2609.28241v1, PDF p. 5, §II B, unnumbered: key-side unitary equivalence of maximally entangled resources

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P22

namespace QAlgorithms.Papers.Independent.Information100.P22

open scoped ComplexConjugate ComplexOrder Matrix

noncomputable section

local instance (p : Prop) : Decidable p := Classical.propDecidable p

/-- PDF p.5: uniqueness of purification gives a key-only unitary. -/
theorem keyUnitaryClass (m k : ℕ) (hm : 1 ≤ m) (hk : 1 ≤ k)
    (R : EuclideanSpace ℂ (Signals m k × Signals m k)) (hR : IsState R)
    (hmax : rhoS R = mixed (Signals m k)) :
    ∃ V : Matrix.unitaryGroup (Signals m k) ℂ,
      R = act (Matrix.kronecker (1 : Op (Signals m k)) (V : Op _)) (bell (Signals m k)) := by sorry

end

end QAlgorithms.Papers.Independent.Information100.P22
