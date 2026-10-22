-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P23_symmetric_sector_dimensions
-- name    : QAlgorithms.Papers.Independent.Gap48.P23.symmetric_sector_dimensions
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T23:02:53.771424+00:00
-- url     : https://prove2.me/theorems/1bb66880-3fed-402f-a0a3-2732db72f8d5
-- title:
--   Lemma D.5.
-- statement:
--   For $\ell\ge0$, $T^\ell(M)$ is the explicit $(\ell+1)$-dimensional normalized-monomial representation (C.9), evaluated on any complex $2\times2$ matrix. Its coordinates are indexed by $0,\ldots,\ell$. Let $V^\ell|w\rangle=|s_\ell(w)\rangle$ be the real Dicke embedding, $\Pi_\ell=V^\ell V^{\ell\dagger}$, and $|\psi^\ell\rangle=\sum_w\sqrt{\binom\ell w}\psi_0^{\ell-w}\psi_1^w|w\rangle$. Empty tensor powers are one-dimensional and $0^0=1$.
--
--   For $\ell\ge1$, in the common first-qubit/rest ambient space, put $\mathcal V=\mathbb C^2\otimes\operatorname{Sym}(\ell)$, $\mathcal V_{\rm UNOT}=\operatorname{Sym}(\ell+1)$ and let $\mathcal V_{\rm Tr}$ be spanned by the source primed Dicke vectors. Then
--   $$\dim\mathcal V=2(\ell+1),\quad\dim\mathcal V_{\rm Tr}=\ell,\quad\dim\mathcal V_{\rm UNOT}=\ell+2,\quad\mathcal V=\mathcal V_{\rm Tr}\oplus\mathcal V_{\rm UNOT}.$$
--   The two summands are orthogonal.
--
--   This supplies a concrete coordinate identity for the representation and symmetric-space constructions.
-- source:
--   Quantum majority vote, arXiv:2211.11729v1, PDF p. 69, Lemma D.5.

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P23

noncomputable section

namespace QAlgorithms.Papers.Independent.Gap48.P23

open MeasureTheory

open scoped ComplexConjugate Matrix ComplexOrder

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

-- Exact frozen coordinate helpers; no paper-local redeclarations.

open QAlgorithms.Papers.Independent.Information100.P58 (Word)

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

open QAlgorithms.Papers.Independent.Information100.P63 (tensorPower)

/-- PDF p.69, Lemma D.5: dimensions and orthogonal direct-sum decomposition. -/
theorem symmetric_sector_dimensions (ell : ℕ) (hell : 1 ≤ ell) :
    Module.finrank ℂ (physicalSymmetricSpace ell) = 2*(ell+1) ∧
    Module.finrank ℂ (traceSubspace ell) = ell ∧
    Module.finrank ℂ (notSubspace ell) = ell+2 ∧
    physicalSymmetricSpace ell = traceSubspace ell ⊔ notSubspace ell ∧
    Disjoint (traceSubspace ell) (notSubspace ell) ∧
    (∀ v ∈ traceSubspace ell, ∀ w ∈ notSubspace ell, inner ℂ v w = 0) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P23

end
