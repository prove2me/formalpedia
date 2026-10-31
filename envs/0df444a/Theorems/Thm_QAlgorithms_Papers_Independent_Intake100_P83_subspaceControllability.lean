-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P83_subspaceControllability
-- name    : QAlgorithms.Papers.Independent.Intake100.P83.subspaceControllability
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T15:23:09.130265+00:00
-- url     : https://prove2.me/theorems/b903c968-b917-4016-a483-718fe6a4989c
-- title:
--   Full controllability on each actual invariant component
-- statement:
--   Let $G$ be an Abelian group and let $A$ be a finite nonempty orthonormal on-site basis, with $d=|A|$. For each $a\in A$, let $\chi_a:G\to\mathbb C$ be a unit-modulus character, so that $u(g)=\operatorname{diag}(\chi_a(g))$ and the physical action on $n$ sites is $U_n(g)=u(g)^{\otimes n}$. Write $\mathcal V_{n,k}$ for the exact finite products of individually $G$-invariant unitaries acting on at most $k$ arbitrary named sites. A product string $r\in A^n$ has character $\chi_r=\prod_j\chi_{r_j}$; a charge sector is the full span of all strings with the same character.
--
--   Assume $2\le k\le n$. Fix one actual irreducible component $\mathcal H_C$ of $\mathcal V_{n,k}$, constructed from its commutant, and let $W$ be any unitary on that entire component. There is an exact finite product $V$ of evolutions $e^{i\theta H}$, with each $H$ Hermitian, $G$-invariant and supported on at most $k$ named sites, for which
--
--   $$
--   V|_{\mathcal H_C}=W.
--   $$
--
--   The action on other components is unconstrained. Thus each component has full unitary controllability by the complete local symmetric Hamiltonian family, without asserting independent full-unitary control of all components simultaneously.
-- source:
--   Theory of Quantum Circuits with Abelian Symmetries, arXiv:2302.12466v3, PDF p. 11, VII, unnumbered consequence: full controllability on each invariant component

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P83

noncomputable section

open scoped BigOperators ComplexConjugate Matrix Kronecker Manifold ContDiff

attribute [local instance] Classical.propDecidable

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

namespace QAlgorithms.Papers.Independent.Intake100.P83

variable {A G : Type*} [Fintype A] [DecidableEq A]

/-- PDF pp.11-12 VII: each actual component is fully controllable with local symmetric
Hamiltonian pulses. Other components are unconstrained; this is not independent U-block
controllability. -/
theorem subspaceControllability [CommGroup G] [Nonempty A] (chi : A → G → ℂ)
    (hchi : IsOnsite chi) (n k : ℕ) (hk : 2 ≤ k) (hkn : k ≤ n) (r : Words A n)
    (W : Matrix {s // component chi n k r s} {s // component chi n k r s} ℂ)
    (hW : W ∈ Matrix.unitaryGroup {s // component chi n k r s} ℂ) :
    ∃ V ∈ controlGroup chi n k,
      V.submatrix (fun s : {s // component chi n k r s} => s.val)
        (fun s : {s // component chi n k r s} => s.val) = W := by sorry

end QAlgorithms.Papers.Independent.Intake100.P83

end
