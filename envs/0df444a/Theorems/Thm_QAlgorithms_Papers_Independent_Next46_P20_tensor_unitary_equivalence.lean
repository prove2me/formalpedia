-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P20_tensor_unitary_equivalence
-- name    : QAlgorithms.Papers.Independent.Next46.P20.tensor_unitary_equivalence
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T15:14:05.736321+00:00
-- url     : https://prove2.me/theorems/98a4f0e7-7a78-4b4a-aa0e-ad8b5f17a049
-- title:
--   Unitary equivalence with the window subspace
-- statement:
--   Let $n\ge1$, let $\mathcal H=L^2(\mathbb R^n)$ and $\mathcal K=L^2(\mathbb R^{2n})$ with Lebesgue measure, and fix a time-independent $\chi\in\mathcal H$ with $\|\chi\|=1$. Set $T_\chi\psi=\psi\otimes\overline\chi$ and $\mathcal H_\chi=\operatorname{Ran}T_\chi$. Then
--   $$
--   T_\chi:\mathcal H\longrightarrow\mathcal H_\chi
--   \quad\text{is unitary}.
--   $$
--   For every linear operator $a:D(a)\subseteq\mathcal H\to\mathcal H$, its phase-space representative has exactly the transported graph $\{(T_\chi\psi,T_\chi a\psi):\psi\in D(a)\}$. Thus $T_\chi$ intertwines $a$ and its representative, including the operator domains. Equalities of wave functions are almost everywhere.
--
--   This specifies the unitary-equivalence clause of the abstract and introduction item (3).
-- source:
--   Quantum mechanics in phase space: The Schr\"odinger and the Moyal representations, arXiv:1209.1850v1, PDF p. 1, Abstract main result: unitary equivalence with configuration space

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P20

noncomputable section

attribute [local instance] Classical.propDecidable

open MeasureTheory

open scoped BigOperators

namespace QAlgorithms.Papers.Independent.Next46.P20

open QAlgorithms.Papers.Independent.Claimed50.P10 (Configuration coordinateDot)

open QAlgorithms.Papers.Independent.Claimed50.P05 (restrictGraph)

open QAlgorithms.Papers.Independent.Claimed50.P37 (PhaseCoordinates)

/-- PDF pp.1,4,6–10: the abstract's unitary-equivalence clause, pinned to
introduction item (3) and Definition 2.7. The codomain is H_chi. -/
theorem tensor_unitary_equivalence {n : ℕ} (hn : 0 < n)
    (chi : ConfigurationL2 n) (hchi : ‖chi‖ = 1) :
    RealizesTensor chi (tensorEmbedding chi) ∧
    (∃ U : ConfigurationL2 n ≃ₗᵢ[ℂ] windowSpace chi,
      ∀ psi, (U psi : PhaseL2 n) = tensorEmbedding chi psi) ∧
    (∀ (a : ConfigurationL2 n →ₗ.[ℂ] ConfigurationL2 n) (psi eta : ConfigurationL2 n),
      (tensorEmbedding chi psi, tensorEmbedding chi eta) ∈
        transportGraph chi (a.graph : Set (ConfigurationL2 n × ConfigurationL2 n)) ↔ (psi, eta) ∈ a.graph) := by sorry

end QAlgorithms.Papers.Independent.Next46.P20

end
