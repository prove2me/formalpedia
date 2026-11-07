-- Prove2me | Theorems.Thm_PathRecording_lemma_3_8
-- name    : PathRecording.lemma_3_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T08:03:45.506383+00:00
-- url     : https://prove2.me/theorems/b1bb5a44-fb12-47f6-832d-7855d33d9e71
-- title:
--   Lemma 3.8 — Schur orthogonality for compact groups
-- statement:
--   Let $G$ be a compact group with Haar probability measure $dg$, and let $(\rho_\lambda)_{\lambda}$ be a family of irreducible continuous unitary representations $\rho_\lambda:G\to U(d_\lambda)$ that are pairwise non-isomorphic for distinct labels. Then for all labels $\lambda,\lambda'$ and basis indices $X,Y$ of $V_\lambda$ and $X',Y'$ of $V_{\lambda'}$,
--   $$\sqrt{d_\lambda}\sqrt{d_{\lambda'}}\int_G\overline{\langle Y|\rho_\lambda(g)|X\rangle}\,\langle Y'|\rho_{\lambda'}(g)|X'\rangle\,dg=\delta_{\lambda,\lambda'}\,\delta_{X,X'}\,\delta_{Y,Y'}.$$
--
--   Equivalently, the functions $\sqrt{d_\lambda}\langle Y|\rho_\lambda(\cdot)|X\rangle$ are orthonormal in $L^2(G)$; this is why the Fourier transform of Definition 3.7 is unitary and why $\Gamma_tF$ is an isometry on $F^{-1}(\mathrm{Tab}_t)$.
--
--   Differences from the source:
--   - generalization: G a compact Lie group with its normalized Haar measure dg → G any compact topological group with a Borel σ-algebra and a left Haar probability measure μ; reason: the Lie structure is never used; a compact Lie group is such a group, and on it (second countable) every left Haar probability measure is the normalized, regular, bi-invariant Haar measure of Definition 3.1; on a general compact group Lean also admits left Haar measures that are not regular, which only enlarges the statement
--   - generalization: λ, λ' ranging over Ĝ, one fixed irrep per isomorphism class → any family of irreducible continuous unitary representations, pairwise non-isomorphic for distinct labels (SymTensorNet.IsIrrep, ¬ SymTensorNet.RepEquiv); reason: the paper's family of representatives is such a family
--   - encoding: δ_{X,X'}, δ_{Y,Y'} across possibly different spaces → equality of the numerical values of the basis indices; reason: for λ = λ' the index sets coincide; for λ ≠ λ' the factor δ_{λ,λ'} is already 0
-- source:
--   Foxman, Lombardi, Ma, Nehoran, Wright, Quantum Lazy Sampling and Path Recording for Any Group, arXiv:2606.30281v2, Lemma 3.8, p.32

import Mathlib
import Definitions.Def_PathRecording_UnitaryRep
import Definitions.Def_SymTensorNet_IrrepCatalogue

set_option autoImplicit false

namespace PathRecording

open MeasureTheory

/-- Foxman, Lombardi, Ma, Nehoran, Wright, *Quantum Lazy Sampling and Path Recording for Any Group*,
arXiv:2606.30281v2, Lemma 3.8 (Schur orthogonality for compact groups), p.32: for a family of
irreducible, pairwise inequivalent, continuous unitary representations `ρ_λ` of a compact group with
normalized Haar measure, and all `λ, λ', X, X', Y, Y'`,
`√d_λ √d_λ' ∫_G \overline{⟨Y|ρ_λ(g)|X⟩} ⟨Y'|ρ_λ'(g)|X'⟩ dg = δ_{λ,λ'} δ_{X,X'} δ_{Y,Y'}`.

**Formalization Note.** The irreps are indexed by an arbitrary type `ι` (the paper's `Ĝ`): distinct
labels carry non-isomorphic irreps (`SymTensorNet.RepEquiv` is equivalence by an invertible
intertwiner). Basis indices of the same label are compared through their values. -/
theorem lemma_3_8 {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] [IsProbabilityMeasure μ]
    {ι : Type*} [DecidableEq ι] (d : ι → ℕ) (π : (l : ι) → UnitaryRep G (d l))
    (hirr : ∀ l, SymTensorNet.IsIrrep (π l).toHom)
    (hineq : ∀ l l', l ≠ l' → ¬ SymTensorNet.RepEquiv (π l).toHom (π l').toHom)
    (l l' : ι) (X Y : Fin (d l)) (X' Y' : Fin (d l')) :
    ((Real.sqrt (d l : ℝ) : ℝ) : ℂ) * ((Real.sqrt (d l' : ℝ) : ℝ) : ℂ) *
        ∫ g, star ((π l).mat g Y X) * (π l').mat g Y' X' ∂μ =
      if l = l' ∧ (X : ℕ) = X' ∧ (Y : ℕ) = Y' then 1 else 0 := by sorry

end PathRecording
