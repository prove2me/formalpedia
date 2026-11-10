-- Prove2me | Theorems.Thm_TolProdTest_eq_56
-- name    : TolProdTest.eq_56
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T03:26:42.637085+00:00
-- url     : https://prove2.me/theorems/e9894ef5-9720-4abb-99d5-78c8539fe260
-- title:
--   Eq. (56) [WRG+26] — Haar representation $h_k(A)=\dim\mathrm{Sym}^k\int\langle u|A|u\rangle^k\,d\mu$
-- statement:
--   Let $D\ge1$, $k\ge1$, and let $A$ be a positive semidefinite operator on $\mathbb C^D$. Then
--
--   $$
--   h_k(A)=\mathrm{Tr}\big(Q_kA^{\otimes k}\big)=\dim\mathrm{Sym}^k(\mathbb C^D)\int\langle u|A|u\rangle^k\,d\mu(u),
--   \qquad \dim\mathrm{Sym}^k(\mathbb C^D)=\binom{k+D-1}{k},
--   $$
--
--   where $\mu$ is the Haar probability measure on unit vectors of $\mathbb C^D$. The paper cites this from [WRG+26, Appendix A] and uses it on the block spaces $\mathcal H_c$ and on the high-eigenvalue subspaces $E_c$ in the proof of Lemma 3.6.
--
--   Differences from the source:
--   - generalization: a positive operator A on H_c → a positive semidefinite A on ℂ^D for every D ≥ 1; reason: H_c ≅ ℂ^{d^{|B_c|}} is an instance; the paper also uses the representation on E_c (62)
--   - encoding: dim Sym^k(ℂ^R) → Nat.choose (k + R - 1) k; reason: the paper's own formula, stated with (47), p.13
--   - encoding: µ_c the Haar probability measure on unit vectors → the published OptimalSpectrum.Entangled.uniformSphere D, Mathlib's sphere surface measure normalized to mass 1, on EuclideanSpace ℂ (Fin D); reason: the unitarily invariant probability measure on the unit sphere of ℂ^D ≅ ℝ^{2D}
--   - encoding: Q_{k,c} the projector onto Sym^k(H_c) → the published QMAPlusGap.symProj = (1/k!) Σ_π P_π (inside hk); reason: the same projector
-- source:
--   Bao, Helsen, Nguyen, Fully tolerant product state testing and closest product state learning, arXiv:2610.01979 (version of October 1st 2026, sha256 9e43ab25…), proof of Lemma 3.6, eq. (56), p.15 (cited from [WRG+26, Appendix A])

import Mathlib
import Definitions.Def_TolProdTest_hk
import Definitions.Def_OptimalSpectrum_Entangled_uniformSphere

set_option autoImplicit false

open Matrix
open scoped ComplexOrder

namespace TolProdTest

/-- **Haar representation of `h_k`, eq. (56)**, Bao, Helsen, Nguyen, *Fully tolerant product state testing and closest product state learning*, arXiv:2610.01979 (version of October 1st 2026, sha256 9e43ab25…), proof of Lemma 3.6, p.15 (cited from [WRG+26, Appendix A]):
"For any positive operator A on H_c, define h_k(A) := Tr(Q_{k,c} A^{⊗k}) = dim Sym^k(H_c) ∫ ⟨u_c|A|u_c⟩^k dµ_c(u_c),
(56) where µ_c is the Haar probability measure on unit vectors in H_c."

**Formalization Note** Stated on a bare space `H = ℂ^D` (`D ≥ 1`), as the paper uses it for `H_c` and for
`E_c`. `µ` is the published `OptimalSpectrum.Entangled.uniformSphere D`, the normalized rotation-invariant surface
measure on the unit sphere of `ℂ^D` (the unitarily invariant probability measure on unit vectors).
`dim Sym^k(ℂ^D) = C(k + D − 1, k)`. `⟨u|A|u⟩ = Σ_{a,b} conj(u_a) A_{ab} u_b`. The identity is an identity of
complex numbers; `k ≥ 1` as in §2.2. -/
theorem eq_56 (D k : ℕ) (hD : 1 ≤ D) (hk1 : 1 ≤ k) (A : Matrix (Fin D) (Fin D) ℂ) (hA : A.PosSemidef) :
    hk k A = ((Nat.choose (k + D - 1) k : ℕ) : ℂ) *
      ∫ u, (star (fun i => u i) ⬝ᵥ (A *ᵥ fun i => u i)) ^ k ∂(OptimalSpectrum.Entangled.uniformSphere D) := by sorry

end TolProdTest
