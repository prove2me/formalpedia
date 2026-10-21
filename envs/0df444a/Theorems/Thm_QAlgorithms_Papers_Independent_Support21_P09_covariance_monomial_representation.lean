-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support21_P09_covariance_monomial_representation
-- name    : QAlgorithms.Papers.Independent.Support21.P09.covariance_monomial_representation
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T03:42:42.217743+00:00
-- url     : https://prove2.me/theorems/f64995b3-95f7-4b62-a0c8-a022d0d394be
-- title:
--   Covariance induces an ordinary monomial representation
-- statement:
--   Let $G$ be finite, $d>0$, and $\phi:G\to U(d)$ an ordinary representation. Let $M\in\mathbb C^{d\times n}$ have nonzero columns $v_j$, with distinct effects $v_jv_j^\dagger$ forming a POVM invariant under $\phi$. For the given, arbitrarily phased columns there exist a permutation homomorphism $\pi:G\to S_n$, scalars $z(g,j)$ of modulus one, and an ordinary unitary representation $R:G\to U(n)$ such that
--
--   $$
--   \phi(g)v_j=z(g,j)v_{\pi(g)j},\qquad R(g)_{ij}=\begin{cases}z(g,j)&i=\pi(g)j,\0&\text{otherwise},\end{cases}\qquad \phi(g)M=MR(g).
--   $$
--
--   Both $R$ and $\pi$ obey their group laws. This expresses covariance as a matrix symmetry while retaining the phases of the chosen column representatives.
-- source:
--   Implementation of group-covariant POVMs by orthogonal measurements, arXiv:quant-ph/0407054v1, PDF p. 8, §3: covariance induces a monomial representation

import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P09

noncomputable section

namespace QAlgorithms.Papers.Independent.Support21.P09

open scoped BigOperators ComplexConjugate

open QAlgorithms.Papers.Independent.Frontier18.P17 (clock)

/-- PDF pp.7–8: covariance gives an ordinary monomial unitary representation, together
with a permutation homomorphism and unit-modulus column phases. -/
theorem covariance_monomial_representation
    {G : Type*} [Group G] [Fintype G] {d n : ℕ} (hd : 0 < d)
    (phi : Rep G (Fin d)) (hphi : UnitaryRep phi)
    (M : Matrix (Fin d) (Fin n) ℂ) (hM : RankOnePOVM M)
    (hdist : Function.Injective (columnEffect M)) (hcov : EffectsCovariant phi M) :
    ∃ R : Rep G (Fin n), ∃ pi : G →* Equiv.Perm (Fin n), ∃ z : G → Fin n → ℂ,
      UnitaryRep R ∧ (∀ g j, ‖z g j‖ = 1) ∧
      (∀ g i j, R g i j = if i = pi g j then z g j else 0) ∧
      (∀ g j i, (phi g).mulVec (fun r => M r j) i = z g j * M i (pi g j)) ∧
      MatrixIntertwines phi R M := by sorry

end QAlgorithms.Papers.Independent.Support21.P09

end
