-- Prove2me | Theorems.Thm_SubspaceConv_lemma_2
-- name    : SubspaceConv.lemma_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T23:17:06.932357+00:00
-- url     : https://prove2.me/theorems/8aa3ba4a-18dd-47c7-8054-7a582bb8ad91
-- title:
--   Lemma 2 — affine Fourier identity $\widehat{\mathsf Ah}_\lambda(D)=\sum_{B\le D}\widehat h_\lambda(B)$
-- statement:
--   Let $H=\mathbb F_q^d$ and let $h_B:H/B\to S$ be tables, one for each direction $B$ with $\dim B\le\ell$. For every direction $D$ of dimension at most $\ell$ and every $\lambda\in D^\circ$,
--   $$\widehat{\mathsf Ah}_\lambda(D)=\sum_{B\le D}\widehat h_\lambda(B),\tag{9}$$
--   where the hat is the Fourier transform (6) and the sum runs over the directions $B\le D$ with $\dim B\le\ell$ (for which $\lambda\in D^\circ\subseteq B^\circ$).
--
--   Fourier transformation in the coset coordinate thus turns the affine containment sum $\mathsf A$ into ordinary subspace zeta transforms, one for each frequency $\lambda$, on the subspaces of $\ker\lambda$.
--
--   **Formalization Note** Stated over any commutative ring $S$ and for any function $\psi:\mathbb F_q\to S$.
--
--   Differences from the source:
--   - generalization: tables in ℂ and a nontrivial additive character ψ : F_q → ℂ → any commutative ring S and any function ψ : F → S; reason: the identity uses only that λ is constant on each D-coset; the paper's ℂ case and the §3.4 ring are instances
--   - encoding: ĥ_λ(B) for B ≤ D with λ ∈ D° → λ transported to B° by the inclusion D° ⊆ B° (annihMono); reason: the same vector λ
-- source:
--   Perles, Weinstein, A Fast Algorithm for Subspace Convolution, STOC 2027 submission manuscript (sha256 a8ffb1b4…604ab2), §3.2, Lemma 2, eq. (9), p.12 (PDF p.13)

import Mathlib
import Definitions.Def_SubspaceConv_SubLE
import Definitions.Def_SubspaceConv_cosetSum
import Definitions.Def_SubspaceConv_annih
import Definitions.Def_SubspaceConv_fourier

namespace SubspaceConv

open Classical in
/-- **Lemma 2** (Affine Fourier identity), eq. (9), Perles–Weinstein, *A Fast Algorithm for Subspace Convolution*, STOC 2027 submission manuscript (sha256 a8ffb1b4…604ab2), §3.2, p.12 (PDF p.13). For
`H = F_q^d` and tables `h_B : H/B → S` with `dim B ≤ ℓ`: for every direction `D` of dimension at
most `ℓ` and every `λ ∈ D°`, `(Ah)^_λ(D) = ∑_{B ≤ D} ĥ_λ(B)`.

**Formalization Note** The sum is over the directions `B` of dimension at most `ℓ` with
`B ≤ D`; for such `B`, `λ ∈ D° ⊆ B°` (`annihMono`). The character `ψ : F → S` is an arbitrary
function into a commutative ring: the identity uses only that `λ` is constant on each
`D`-coset. -/
theorem lemma_2 (F : Type) [Field F] [Fintype F] [DecidableEq F] {S : Type*} [CommRing S]
    (ψ : F → S) (d ℓ : ℕ) (h : (B : SubLE F d ℓ) → (Fin d → F) ⧸ B.1 → S)
    (D : SubLE F d ℓ) (lam : annih D.1) :
    fourier ψ (cosetSum h D) lam =
      ∑ B : SubLE F d ℓ,
        if hB : B.1 ≤ D.1 then fourier ψ (h B) (annihMono hB lam) else 0 := by sorry

end SubspaceConv
