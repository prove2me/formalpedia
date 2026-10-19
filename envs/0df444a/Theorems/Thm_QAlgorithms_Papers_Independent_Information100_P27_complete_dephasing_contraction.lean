-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P27_complete_dephasing_contraction
-- name    : QAlgorithms.Papers.Independent.Information100.P27.complete_dephasing_contraction
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T10:19:07.651093+00:00
-- url     : https://prove2.me/theorems/cd175487-2901-42c4-8e4c-5e026d11cf07
-- title:
--   Theorem 9.2: complete product-dephasing entropy contraction
-- statement:
--   Let $n\ge1$, let $R$ be any nonempty finite dimensional auxiliary system, and let $\theta$ be any density matrix on $n$ qubits and $R$. For $0\le\gamma\le1$, let $Z_\gamma$ preserve the diagonal entries of a qubit matrix and multiply its off-diagonal entries by $\gamma$. Set $\xi=(Z_\gamma^{\otimes n}\otimes\mathrm{id}_R)(\theta)$ and $C(\eta)=H((\Delta^{\otimes n}\otimes\mathrm{id}_R)(\eta))-H(\eta)$, where $\Delta$ completely dephases each qubit. Then
--
--   $$
--   C(\xi)\le\gamma^2 C(\theta).
--   $$
--
--   The reference is preserved in both joint entropies. Arbitrary correlations and singular states are permitted; no full-rank or product-state hypothesis is imposed.
-- source:
--   Static classical-quantum- entanglement trade-offs: an entropic converse and single-letter characterizations, arXiv:2609.23298v1, PDF p. 44, Theorem 9.2: complete product-dephasing entropy contraction

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P27

noncomputable section

open scoped ComplexConjugate ComplexOrder

attribute [local instance] Classical.decEq Classical.propDecidable

namespace QAlgorithms.Papers.Independent.Information100.P27

/-- arXiv:2609.23298v1 PDF p.44, Theorem 9.2 (proof pp.78-80): complete
product-dephasing contraction, including singular and correlated inputs. -/
theorem complete_dephasing_contraction {R : Type} [Fintype R] [Nonempty R]
    (n : ℕ) (hn : 0 < n) (gamma : ℝ) (hgamma0 : 0 ≤ gamma) (hgamma1 : gamma ≤ 1)
    (theta : Matrix (Qubits n × R) (Qubits n × R) ℂ) (htheta : IsDensityMatrix theta) :
    completeCoherence n (productDephasing n gamma theta) ≤ gamma ^ 2 * completeCoherence n theta := by sorry

end QAlgorithms.Papers.Independent.Information100.P27

end
