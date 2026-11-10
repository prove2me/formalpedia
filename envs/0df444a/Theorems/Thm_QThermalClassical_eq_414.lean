-- Prove2me | Theorems.Thm_QThermalClassical_eq_414
-- name    : QThermalClassical.eq_414
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T23:10:51.163272+00:00
-- url     : https://prove2.me/theorems/d47ce78d-563c-4651-8827-6c1ed324690d
-- title:
--   Eq. (414) — anticommuting operators: $\sum_i\mathrm{Tr}(C_i\sigma)^2\le1$
-- statement:
--   Let $C_1,\dots,C_m$ be pairwise anticommuting Hermitian operators with $C_i^2=I$ on a finite-dimensional Hilbert space, and let $\sigma$ be a state ($\sigma\succeq0$, $\mathrm{Tr}\,\sigma=1$). Then
--   $$
--   \sum_i\mathrm{Tr}(C_i\sigma)^2\le1 .
--   $$
--
--   This bounds the correlation $\left|\mathrm{Tr}\big((\sigma_A\otimes\sigma_B)\sum_iQ_{x,i}\big)\right|\le1$ of product states in the proof of Theorem 35 (eqs. (413)–(415)).
--
--   Differences from the source:
--   - reading: pairwise anticommuting operators $\{C_i\}$ → Hermitian $C_i$ with $C_i^2=I$ and $C_iC_j=-C_jC_i$ for $i\neq j$; reason: the proof uses $(\sum_i\mathrm{Tr}(C_i\sigma)C_i)^2=(\sum_i\mathrm{Tr}(C_i\sigma)^2)I$ and real traces; the paper applies it to Pauli strings; without it the bound fails (one operator $C=2I$ gives $4$)
--   - generalization: operators on $n$ qubits → operators on any finite-dimensional $\mathbb C^d$, a finite family; reason: the proof is dimension-free
--   - encoding: $\mathrm{Tr}(C_i\sigma)^2$ → $(\mathrm{Re}\,\mathrm{Tr}(C_i\sigma))^2$; reason: $\mathrm{Tr}(C_i\sigma)$ is real for Hermitian $C_i$ and $\sigma$
-- source:
--   J. Cotler, H. Putterman, A. Zlokapa, When quantum thermal states look classical, arXiv:2607.28536 (held version, sha256 7491d0b2…), proof of Theorem 35, eq. (414) and the sentence after it, p.85

import Mathlib

set_option autoImplicit false

open scoped ComplexOrder

namespace QThermalClassical

/-- **Eq. (414) (anticommuting operators).** Pairwise anticommuting operators `{C_i}` satisfy,
for any state `σ`, `Σ_i Tr(C_i σ)² ≤ 1`.

Source: J. Cotler, H. Putterman, A. Zlokapa, *When quantum thermal states look classical*,
arXiv:2607.28536 (held version, sha256 7491d0b2…), proof of Theorem 35, eq. (414) and the sentence after it, p.85.

**Formalization Note.** The operators are Hermitian involutions (`C_i^† = C_i`,
`C_i² = I`), as the Pauli strings to which the paper applies (414) are, and as its proof uses
(`(Σ_i Tr(C_iσ) C_i)² = (Σ_i Tr(C_iσ)²) I`); a state is a positive semidefinite matrix of trace
`1`. The family is finite and the Hilbert space is any finite-dimensional `ℂ^d`. For Hermitian
`C_i` and `σ`, `Tr(C_iσ)` is real, and the statement uses its real part. -/
theorem eq_414 {d ι : Type} [Fintype d] [DecidableEq d] [Fintype ι]
    (C : ι → Matrix d d ℂ) (σ : Matrix d d ℂ)
    (hherm : ∀ i, (C i).IsHermitian) (hinv : ∀ i, C i * C i = 1)
    (hanti : ∀ i j, i ≠ j → C i * C j = -(C j * C i))
    (hσ : σ.PosSemidef) (htr : σ.trace = 1) :
    ∑ i, ((C i * σ).trace.re) ^ 2 ≤ 1 := by sorry

end QThermalClassical
