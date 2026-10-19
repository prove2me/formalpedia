-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P38_spectral_variational_advantage_bound
-- name    : QAlgorithms.Papers.Independent.Information100.P38.spectral_variational_advantage_bound
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T11:06:49.299556+00:00
-- url     : https://prove2.me/theorems/9b1d8521-017e-4736-b3d7-2da74f3082b2
-- title:
--   Theorem 2 / Eq.(34)
-- statement:
--   Let $d,n\ge1$, let $M$ be a POVM, and let $H$ have weakly increasing real energies $E_0,\ldots,E_{d-1}$. Let $\Phi_M$ be its coarse-graining channel, with zero-effect contributions omitted, and let $\Delta$ be dephasing in the energy basis. Then
--
--   $$A_H^M\le\sum_{k=1}^{d-1}(E_k-E_{k-1})\max_{\substack{0\le Q\le I\\\operatorname{Tr}Q=k}}\lambda_{\max}\bigl(\Phi_M(Q)-\Delta(\Phi_M(Q))\bigr).$$
--
--   The maximum is over effects of the indicated trace. The sum is empty when $d=1$. This variational estimate separates the Hamiltonian gaps from measurement-dependent spectral quantities.
-- source:
--   All coherent measurements provide observational ergotropic advantage, arXiv:2609.18735v1, PDF p. 6, Theorem 2 / Eq.(34)

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P38

noncomputable section

namespace QAlgorithms.Papers.Independent.Information100.P38

open scoped ComplexConjugate Matrix

/-- Paper pp.6–7, Theorem 2, Eq.(34): spectral variational bound. The double sum
contains each adjacent pair exactly once, so dimension one gives an empty sum. -/
theorem spectral_variational_advantage_bound {d n : ℕ} (hd : 0 < d) (hn : 0 < n)
    (E : Fin d → ℝ) (hE : Monotone E)
    (M : Fin n → Matrix (Fin d) (Fin d) ℂ) (hM : IsPOVM M) :
    observationalAdvantage E M ≤ ∑ i : Fin d, ∑ j : Fin d,
      if j.val = i.val + 1 then (E j - E i) * spectralAdvantageTerm M j.val else 0 := by sorry

end QAlgorithms.Papers.Independent.Information100.P38

end
