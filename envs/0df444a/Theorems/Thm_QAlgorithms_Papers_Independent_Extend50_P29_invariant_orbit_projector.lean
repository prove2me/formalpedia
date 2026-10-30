-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P29_invariant_orbit_projector
-- name    : QAlgorithms.Papers.Independent.Extend50.P29.invariant_orbit_projector
-- status  : Proved
-- author  : @Gohan
-- created : 2026-10-29T08:17:00.540801+00:00
-- url     : https://prove2.me/theorems/0ea91c79-7944-41ff-902b-d37d0e951b06
-- title:
--   Appendix C construction: invariant orbit basis and projector marginals, Eq.(C1)
-- statement:
--   Let $G$ be finite, $d=|G|\ge1$, and $n\ge1$. On the regular group basis define
--   $$M|h_1,\ldots,h_n\rangle=\frac1{\sqrt d}\sum_{g\in G}|gh_1,\ldots,gh_n,g\rangle,\qquad \Pi=MM^\dagger.$$
--   Then $M^\dagger M=I$, its range is exactly the subspace invariant under the diagonal left regular action, and $\Pi$ is a Hermitian idempotent. For every one of the $n+1$ registers,
--   $$\operatorname{Tr}_j\Pi=I_{\{0,\ldots,n\}\setminus\{j\}}.$$
--   This identifies the invariant-orbit probability space used in Appendix C. The projector is unnormalized: $\operatorname{Tr}\Pi=d^n$, while $\Pi/d^n$ is the mean density matrix of a Haar invariant state.
-- source:
--   Error Correction of Quantum Reference Frame Information, arXiv:1709.04471v1, PDF p. 13, Appendix C construction: invariant orbit basis and projector marginals, Eq.(C1)

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P29

noncomputable section

open MeasureTheory MeasureTheory.Measure

open scoped Matrix ComplexConjugate ComplexOrder Matrix.Norms.L2Operator

attribute [local instance] Classical.propDecidable Classical.decEq

namespace QAlgorithms.Papers.Independent.Extend50.P29

open QAlgorithms.Papers.Independent.Information100.P32 (evolution)

open QAlgorithms.Papers.Independent.Next46.P39 (inverseSqrt rectAct)

open QAlgorithms.Papers.Independent.Support21.P09 (groupLeftRegular)

/-- PDF p.13, Eq.(C1): M is an isometry onto exactly the invariant subspace;
its projector becomes identity after tracing any one register (no density normalization). -/
theorem invariant_orbit_projector
    (G : Type) [Group G] [Fintype G] {n : ℕ} (hn : 1 ≤ n) :
    (invariantOrbitMap G n)ᴴ * invariantOrbitMap G n = 1 ∧
    (∀ ψ : EuclideanSpace ℂ (Fin (n + 1) → G),
      RegularInvariant ψ ↔ ∃ φ : EuclideanSpace ℂ (Fin n → G), rectAct (invariantOrbitMap G n) φ = ψ) ∧
    (orbitProjector G n)ᴴ = orbitProjector G n ∧
    orbitProjector G n * orbitProjector G n = orbitProjector G n ∧
    (∀ j : Fin (n + 1), dependentRegisterTrace (H := fun _ : Fin (n + 1) => G)
      (Finset.univ.erase j) (orbitProjector G n) = 1) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P29

end
