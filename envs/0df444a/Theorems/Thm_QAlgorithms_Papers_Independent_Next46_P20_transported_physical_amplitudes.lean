-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P20_transported_physical_amplitudes
-- name    : QAlgorithms.Papers.Independent.Next46.P20.transported_physical_amplitudes
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T15:21:34.25515+00:00
-- url     : https://prove2.me/theorems/e53b7fd1-2cc2-4a87-9411-fde9c1971978
-- title:
--   Equality of matrix elements and transition amplitudes
-- statement:
--   Let $n\ge1$, fix a unit window $\chi$, and let $A$ be the representative of a linear operator $a$ with its transported domain. For every $\psi\in L^2(\mathbb R^n)$ and $\phi\in D(a)$,
--   $$
--   \langle T_\chi\psi,A T_\chi\phi\rangle=\langle\psi,a\phi\rangle.
--   $$
--   For every nonzero eigenfunction $\psi_\lambda\in D(a)$ with $a\psi_\lambda=\lambda\psi_\lambda$, one also has
--   $$
--   \langle T_\chi\psi,T_\chi\psi_\lambda\rangle=\langle\psi,\psi_\lambda\rangle.
--   $$
--   The first assertion does not require eigenfunctions to exist. These equalities give the same expectation values and transition amplitudes; the usual probability interpretation uses normalized states.
-- source:
--   Quantum mechanics in phase space: The Schr\"odinger and the Moyal representations, arXiv:1209.1850v1, PDF p. 10, Corollary 2.11

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P20

noncomputable section

attribute [local instance] Classical.propDecidable

open MeasureTheory

open scoped BigOperators

namespace QAlgorithms.Papers.Independent.Next46.P20

open QAlgorithms.Papers.Independent.Claimed50.P10 (Configuration coordinateDot)

open QAlgorithms.Papers.Independent.Claimed50.P05 (restrictGraph)

open QAlgorithms.Papers.Independent.Claimed50.P37 (PhaseCoordinates)

/-- PDF p.10, Corollary 2.11: matrix elements and transition amplitudes agree.
The operator acts only on the supplied domain vector phi. -/
theorem transported_physical_amplitudes {n : ℕ} (hn : 0 < n)
    (chi : ConfigurationL2 n) (hchi : ‖chi‖ = 1)
    (a : ConfigurationL2 n →ₗ.[ℂ] ConfigurationL2 n) (psi : ConfigurationL2 n) :
    (∀ phi : a.domain,
      inner ℂ (tensorEmbedding chi psi) (tensorEmbedding chi (a phi)) =
        inner ℂ psi (a phi)) ∧
    (∀ (lambda : ℂ) (psiLambda : ConfigurationL2 n),
      (psiLambda, lambda • psiLambda) ∈ a.graph → psiLambda ≠ 0 →
      inner ℂ (tensorEmbedding chi psi) (tensorEmbedding chi psiLambda) =
        inner ℂ psi psiLambda) := by sorry

end QAlgorithms.Papers.Independent.Next46.P20

end
