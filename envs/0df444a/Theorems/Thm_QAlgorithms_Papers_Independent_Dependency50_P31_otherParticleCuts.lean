-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P31_otherParticleCuts
-- name    : QAlgorithms.Papers.Independent.Dependency50.P31.otherParticleCuts
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T14:42:33.941696+00:00
-- url     : https://prove2.me/theorems/5e70d46e-772d-4f81-a893-8fb8c4ab0238
-- title:
--   Swapping maximizers to other single-particle cuts
-- statement:
--   Let $\nu$ have $N\ge2$ boxes and let $d\ge c_1$. Let $W_\nu$ be the full isotypic component and put $M=\sup_{\phi\in W_\nu,\ \|\phi\|=1}\lambda_1(\phi)^2$ for the final-particle cut. Fix $1\le k<N$, let $U_{kN}$ swap physical factors $k$ and $N$, and suppose a unit vector $\psi\in W_\nu$ attains $M$. Define $\rho_k(\phi)=\rho_N(U_{kN}\phi)$. Then
--
--   $$
--   \eta=U_{kN}\psi\in W_\nu,\qquad\|\eta\|=1,\qquad
--   \|\rho_k(\eta)\|_{\mathrm{op}}=M,\qquad
--   \forall\phi\in W_\nu,\ \|\phi\|=1\Longrightarrow
--   \|\rho_k(\phi)\|_{\mathrm{op}}\le\|\rho_k(\eta)\|_{\mathrm{op}}.
--   $$
--
--   Thus swapping any final-cut maximizer gives a maximizer for the chosen particle. This does not assert equality of different marginal spectra of one fixed state.
-- source:
--   Lower bound on entanglement in subspaces defined by Young diagrams, arXiv:1805.00364v2, PDF p. 6, Remark 4

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P31

noncomputable section

namespace QAlgorithms.Papers.Independent.Dependency50.P31

open scoped ComplexConjugate

open QAlgorithms.Papers.Independent.Information100.P58 (Word)

attribute [local instance] Classical.propDecidable

/-- Remark 4, arXiv:1805.00364v2 PDF p.6. Swapping any last-cut maximizer
produces a maximizer for the specified other particle. No assertion identifies
different marginal spectra of one fixed state. -/
theorem otherParticleCuts {d n : ℕ} (hn : 2 ≤ n) (nu : Schur.Partition d n)
    (k : Fin n) (hk : k.val ≠ n-1) (psi : H d n)
    (hpsi : psi ∈ isotypicSpace nu) (hunit : ‖psi‖ = 1)
    (hmax : largestSchmidtSq psi = subspaceOptimum (isotypicSpace nu)) :
    swapToLast (by omega) k psi ∈ isotypicSpace nu ∧
    ‖swapToLast (by omega) k psi‖ = 1 ∧
    specNorm (particleMarginal (by omega) k (swapToLast (by omega) k psi)) =
      subspaceOptimum (isotypicSpace nu) ∧
    (∀ phi ∈ isotypicSpace nu, ‖phi‖ = 1 →
      specNorm (particleMarginal (by omega) k phi) ≤
        specNorm (particleMarginal (by omega) k (swapToLast (by omega) k psi))) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P31

end
