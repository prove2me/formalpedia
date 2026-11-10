-- Prove2me | Theorems.Thm_TolProdTest_eq_66
-- name    : TolProdTest.eq_66
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T03:26:50.810475+00:00
-- url     : https://prove2.me/theorems/baedd146-d6db-4e16-9711-ea5226846ce4
-- title:
--   Eq. (66) [IMA21] — $h_k(\sigma)\le\dim\mathrm{Sym}^k(\mathbb C^R)/R^k$ for $0\le\sigma\le I/R$, $\mathrm{Tr}\,\sigma\le1$
-- statement:
--   Let $D\ge1$, $R\ge1$, $k\ge1$, and let $\sigma$ be an operator on $\mathbb C^D$ with
--
--   $$
--   0\le\sigma\le\frac IR,\qquad \mathrm{Tr}\,\sigma\le1 .
--   $$
--
--   Then
--
--   $$
--   h_k(\sigma)\ \le\ \frac{\dim\mathrm{Sym}^k(\mathbb C^R)}{R^k}=\frac{1}{R^k}\binom{k+R-1}{k}.
--   $$
--
--   The paper derives it from the weak-majorization inequality for complete homogeneous symmetric polynomials [IMA21, Corollary 3.3]; it bounds each discarded part in Lemma 3.6 (ii).
--
--   Differences from the source:
--   - generalization: σ_c = Tr_{−c} ω^lo_c on H_c with (65), R ≥ 2 (Lemma 3.6) → any σ on ℂ^D, D ≥ 1, with 0 ≤ σ ≤ I/R and Tr σ ≤ 1, any R ≥ 1; reason: (65) are the only properties of σ_c the step uses; σ_c and R ≥ 2 are instances
--   - encoding: dim Sym^k(ℂ^R) → Nat.choose (k + R - 1) k; reason: the paper's own formula, stated with (47), p.13
--   - encoding: h_k(σ_c) ≤ …, 0 ≤ σ ≤ I/R, Tr σ ≤ 1 → (hk k σ).re ≤ …; σ.PosSemidef, (R⁻¹ • 1 − σ).PosSemidef, σ.trace.re ≤ 1; reason: h_k and the trace are real for σ ≥ 0; ≤ is the Loewner order (p.8)
-- source:
--   Bao, Helsen, Nguyen, Fully tolerant product state testing and closest product state learning, arXiv:2610.01979 (version of October 1st 2026, sha256 9e43ab25…), proof of Lemma 3.6 (ii), eqs. (65)–(66), p.16 (from [IMA21, Corollary 3.3])

import Mathlib
import Definitions.Def_TolProdTest_hk

set_option autoImplicit false

open Matrix
open scoped ComplexOrder

namespace TolProdTest

/-- **Bound on the discarded part, eq. (66)**, Bao, Helsen, Nguyen, *Fully tolerant product state testing and closest product state learning*, arXiv:2610.01979 (version of October 1st 2026, sha256 9e43ab25…), proof of Lemma 3.6 (ii), p.16 (from [IMA21, Corollary 3.3]):
"0 ≤ σ_c ≤ Π^lo_c ρ_c Π^lo_c ≤ I/R, Tr σ_c ≤ 1. (65) Pad the eigenvalues of σ_c and a vector with R entries 1/R by
zeros to a common length. The former are weakly majorized by the latter, since the sum of their j largest values is
at most min{j/R, 1}. The weak-majorization inequality for complete homogeneous symmetric polynomials [IMA21,
Corollary 3.3] therefore bounds h_k(σ_c) by its value on this vector. The normalization in that result cancels
because the vectors have the same length, giving h_k(σ_c) ≤ dim Sym^k(C^R)/R^k. (66)"

**Formalization Note** Stated for any operator `σ` on `ℂ^D` with `0 ≤ σ ≤ I/R` (Loewner order) and `Tr σ ≤ 1`,
integers `R ≥ 1`, `k ≥ 1`; `h_k(σ) = Tr(Q_k σ^{⊗k})` (56), whose real part is taken (it is real for `σ ≥ 0`).
`dim Sym^k(ℂ^R) = C(k + R − 1, k)`. -/
theorem eq_66 (D R k : ℕ) (hD : 1 ≤ D) (hR : 1 ≤ R) (hk1 : 1 ≤ k) (σ : Matrix (Fin D) (Fin D) ℂ)
    (hσ : σ.PosSemidef) (hσR : ((R : ℂ)⁻¹ • (1 : Matrix (Fin D) (Fin D) ℂ) - σ).PosSemidef)
    (htr : σ.trace.re ≤ 1) :
    (hk k σ).re ≤ (Nat.choose (k + R - 1) k : ℝ) / (R : ℝ) ^ k := by sorry

end TolProdTest
