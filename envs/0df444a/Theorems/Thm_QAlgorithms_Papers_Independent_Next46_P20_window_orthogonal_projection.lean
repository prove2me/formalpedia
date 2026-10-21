-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P20_window_orthogonal_projection
-- name    : QAlgorithms.Papers.Independent.Next46.P20.window_orthogonal_projection
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T15:17:25.50751+00:00
-- url     : https://prove2.me/theorems/b5e5b734-e1e5-4675-88b9-83d48ef20a36
-- title:
--   Orthogonal projection and Hilbert window subspace
-- statement:
--   Fix $n\ge1$ and a unit window $\chi\in L^2(\mathbb R^n)$. Write $T=T_\chi$ and $P=TT^*$. Then
--   $$
--   P^*=P,\qquad P^2=P,\qquad \operatorname{Ran}P=\mathcal H_\chi=\operatorname{Ran}T.
--   $$
--   The space $\mathcal H_\chi$ is a closed Hilbert subspace of phase-space $L^2$, with $\langle T\phi,T\psi\rangle=\langle\phi,\psi\rangle$. Moreover, $T^*T\psi=\psi$ for every configuration vector and $TT^*\Psi=\Psi$ for every $\Psi\in\mathcal H_\chi$.
--
--   The inverse assertions include Remark 2.4 on the same page.
-- source:
--   Quantum mechanics in phase space: The Schr\"odinger and the Moyal representations, arXiv:1209.1850v1, PDF p. 8, Corollary 2.5

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P20

noncomputable section

attribute [local instance] Classical.propDecidable

open MeasureTheory

open scoped BigOperators

namespace QAlgorithms.Papers.Independent.Next46.P20

open QAlgorithms.Papers.Independent.Claimed50.P10 (Configuration coordinateDot)

open QAlgorithms.Papers.Independent.Claimed50.P05 (restrictGraph)

open QAlgorithms.Papers.Independent.Claimed50.P37 (PhaseCoordinates)

/-- PDF p.8, Corollary 2.5 and Remark 2.4: orthogonal projection, closed range,
preserved inner product, and the two inverse identities on their stated domains. -/
theorem window_orthogonal_projection {n : ℕ} (hn : 0 < n)
    (chi : ConfigurationL2 n) (hchi : ‖chi‖ = 1) :
    let T := tensorEmbedding chi
    let P := T.comp T.adjoint
    P.adjoint = P ∧ P.comp P = P ∧
    P.toLinearMap.range = windowSpace chi ∧
    IsClosed (windowSpace chi : Set (PhaseL2 n)) ∧
    (∀ phi psi : ConfigurationL2 n, inner ℂ (T phi) (T psi) = inner ℂ phi psi) ∧
    (∀ psi : ConfigurationL2 n, T.adjoint (T psi) = psi) ∧
    (∀ Psi : PhaseL2 n, Psi ∈ windowSpace chi → T (T.adjoint Psi) = Psi) := by sorry

end QAlgorithms.Papers.Independent.Next46.P20

end
