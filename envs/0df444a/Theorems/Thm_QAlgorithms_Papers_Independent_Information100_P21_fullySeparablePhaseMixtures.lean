-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P21_fullySeparablePhaseMixtures
-- name    : QAlgorithms.Papers.Independent.Information100.P21.fullySeparablePhaseMixtures
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T10:00:51.272631+00:00
-- url     : https://prove2.me/theorems/e3dda78e-b07e-4608-82ea-e9e3b11b84ce
-- title:
--   X.23 — Lemma X.23 (Explicit fully separable phase mixtures). Both σ+ and σ− belong to FSN for the n-qubit partition.
-- statement:
--   For $n\ge2$, set $D=2^n$ and $C_n=|0^n\rangle\langle1^n|+|1^n\rangle\langle0^n|$. Then
--   $$\sigma_\pm=(I_D\pm C_n)/D\in\mathrm{FS}_n.$$
--   Full separability is among the individual qubits. The source proves this by averaging $3^{n-1}$ product phase projectors; the theorem asserts membership without requiring a chosen decomposition.
-- source:
--   The Minimal Dimension of Entangled -Noise Advantage, arXiv:2609.28367v1, PDF p. 29, X.23 — Lemma X.23 (Explicit fully separable phase mixtures). Both σ+ and σ− belong to FSN for the n-qubit partition.

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P21

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder ENNReal

namespace QAlgorithms.Papers.Independent.Information100.P21

attribute [local instance] Classical.propDecidable Classical.decEq

/-- arxiv:2609.28367v1, PDF p. 29, Lemma X.23 (Explicit fully separable phase mixtures). Both σ+ and σ− belong to FSN for the n-qubit partition.. -/
theorem fullySeparablePhaseMixtures (n : ℕ) (hn : 2≤n) :
  phaseMixture n true ∈ fs (fun _ : Fin n => 2) ∧
    phaseMixture n false ∈ fs (fun _ : Fin n => 2) := by sorry

end QAlgorithms.Papers.Independent.Information100.P21

end
