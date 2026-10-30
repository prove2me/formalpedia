-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P24_inducedFourier_blockDiagonalizes
-- name    : QAlgorithms.Papers.Independent.Extend50.P24.inducedFourier_blockDiagonalizes
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T17:46:46.213546+00:00
-- url     : https://prove2.me/theorems/8828b013-bc74-4a93-9089-42ee2b5b10df
-- title:
--   Padded Fourier transform of an induced irreducible representation
-- statement:
--   Let $G$ be a finite group, $H\leq G$, and $\sigma$ a unitary irreducible representation of $H$. Fix orthonormal Fourier bases for $H$ and $G$, and a left-coset transversal $\{t_c:c\in C\}$ with the bijection $(c,h)\mapsto t_ch$. Fix a multiplicity coordinate $u$ in the $\sigma$ block of $\mathbb C[H]$, independently of the input vector. Write $F_H,F_G$ for the normalized group Fourier transforms, using the irrep coordinate before the multiplicity coordinate.
--
--   Define $J_{\sigma,u}$ by inserting $|\sigma,v,u\rangle$, applying $F_H^\dagger$ to the subgroup register, and relabelling $|c,h\rangle$ as $|t_ch\rangle$. Set $M=F_GJ_{\sigma,u}$. For $g\in G$, the induced action is determined by $gt_c=t_{c'}h$: it sends $|c,v\rangle$ to $|c',\sigma(h)v\rangle$. Then
--
--   $$
--   M^\dagger M=I,\qquad
--   M\,\operatorname{Ind}_H^G(\sigma)(g)v=
--   \left(\bigoplus_\lambda\rho_\lambda(g)\otimes I\right)Mv
--   \quad\text{for every }g\in G\text{ and every }v.
--   $$
--
--   Thus the specified three-step map gives an isometric block diagonalization in the padded $G$-Fourier space. The relabelling $|c,h\rangle\mapsto|t_ch\rangle$ is part of the map. No general runtime claim is made, and clean-ancilla compression is not asserted without the additional ordering condition discussed in the source.
--
--   This is the general induced-transform construction used before the specialization to permutation modules.
-- source:
--   An efficient high dimensional quantum Schur transform, arXiv:1804.00055v2, PDF p. 11, §3.3 unnumbered construction: Fourier transform for an induced irrep

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P24

noncomputable section

open scoped Matrix ComplexConjugate

namespace QAlgorithms.Papers.Independent.Extend50.P24

attribute [local instance] Classical.propDecidable

open QAlgorithms.Papers.Independent.Renew46.P26 (boxContent)

/-- §3.3, PDF pp.10-11: the specified three-step construction is an isometric
padded block diagonalization for every finite group and unitary sigma.
No general efficiency or automatic clean-ancilla removal is asserted. -/
theorem inducedFourier_blockDiagonalizes
    {G C : Type*} [Group G] [Fintype G] [Fintype C]
    (H : Subgroup G) [Fintype H] (T : LeftTransversal H C)
    (DG : FourierData G) (DH : FourierData H)
    (hG : IsUnitaryBetween (groupFourier DG))
    (hH : IsUnitaryBetween (groupFourier DH))
    (sigma : Fin DH.labels) (u : Fin (DH.dimension sigma)) :
    let M := inducedFourier H T DG DH sigma u
    Mᴴ * M = 1 ∧
    ∀ g (v : EuclideanSpace ℂ (C × Fin (DH.dimension sigma))),
      applyMatrix M (QAlgorithms.act (inducedAction H T DH sigma g) v) =
        fourierAction DG g (applyMatrix M v) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P24

end
