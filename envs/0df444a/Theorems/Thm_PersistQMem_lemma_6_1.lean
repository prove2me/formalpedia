-- Prove2me | Theorems.Thm_PersistQMem_lemma_6_1
-- name    : PersistQMem.lemma_6_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T08:48:02.573581+00:00
-- url     : https://prove2.me/theorems/1b41dd1e-dbeb-4649-b7d1-da873cd23d76
-- title:
--   Lemma 6.1 — joint variance contraction: $\|F^*X\|^2+\beta^{-1}\sum_jp_j\ell_j(X)^2\le\|X\|_\sigma^2$, $0\preceq C\preceq\beta\Delta$, $0\preceq\Delta\preceq I$, $\operatorname{rank}F\le2r-2$
-- statement:
--   Fix the data of Definition 2.1, a complete refined instrument $\Phi(Z)=\bigoplus_aM_aZM_a^*$ with entering memory $\mathbb C^r$ (21), and a unit vector $u\in\mathbb C^r$. Let $\sigma=\Phi(uu^*\otimes\tau)$, $\delta_j=\Phi(uu^*\otimes G_j/D)$, $H_\sigma$ the variance Hilbert space of (24), and $F^*X=Q_uN_0^*(X)u$, $\ell_j(X)=\operatorname{Tr}(\delta_jX)$ (25). Then:
--
--   1. $F^*$ and every $\ell_j$ are well defined on $H_\sigma$;
--   2. for every Hermitian recorded test $X$,
--   $$\|F^*X\|^2+\frac1\beta\sum_jp_j\ell_j(X)^2\le\|X\|_\sigma^2;\tag{26}$$
--   3. with $c_j\in H_\sigma$ the Riesz representer of $\ell_j$, $F$ the real adjoint of $F^*$, $C=\sum_jp_j|c_j\rangle\langle c_j|$ and $\Delta=I-FF^*$ (27),
--   $$0\preceq C\preceq\beta\Delta,\qquad0\preceq\Delta\preceq I,\qquad\operatorname{rank}F\le2r-2.\tag{28}$$
--
--   The lemma separates the variance a test spends on directions already held in memory from the variance available to detect the source.
--
--   Differences from the source:
--   - encoding: H_σ, the quotient of Hermitian recorded tests by zero-variance tests → the range of the isometric real-linear map π X = ⊕_a (X_a − Tr(σX) I) L_a in real coordinates (Hsig); maps on tests are transported through a fixed linear section; reason: π is isometric for ⟨·,·⟩_σ and its kernel is the zero-variance tests, so its range is the quotient; maps that vanish on zero-variance tests do not depend on the section
--   - encoding: “well-defined on H_σ” → F* and ℓ_j, transported to H_σ through the section, agree with the test-level maps on the class of every Hermitian test; reason: equivalent to vanishing on zero-variance tests
--   - encoding: F* with values in u^⊥ (real dimension 2r − 2) → values in real coordinates of all of C^r; reason: the values lie in u^⊥ because of Q_u; ‖F*X‖, F F* and rank F are unchanged
--   - encoding: operator inequalities ⪯ on H_σ, rank F → LinearMap.IsPositive of the differences; finrank of the range of F (2r − 2 in ℕ); reason: Lean convention; r ≥ 1 because a unit vector exists, so no truncation
--   - encoding: unit vector u ∈ C^r → u : Fin r → ℂ with star u ⬝ᵥ u = 1; reason: Lean convention; same vectors
--   - generalization: entering memory C^r with r ≤ K (§6.2 standing assumption, p.19) → no relation between r and K is assumed; reason: the statement involves K only through the instrument's output bound k_a ≤ K, which also holds with K replaced by max(r, K), so every instance is an instance of the source's lemma at that memory bound; r ≤ K is the source's case
-- source:
--   Tao, Shen, Structural Lower Bounds for Quantum Property Estimation with Persistent Memory, STOC 2027 submission (manuscript of 2026-11-03, sha256 6d48ad24…), Lemma 6.1, (26)–(28), p.20 (PDF p.23)

import Mathlib
import Definitions.Def_PersistQMem_Hsig

open scoped Matrix ComplexOrder InnerProductSpace

namespace PersistQMem

/-- **Lemma 6.1 (Joint variance contraction), p.20** (Tao, Shen, *Structural Lower Bounds for
Quantum Property Estimation with Persistent Memory*, STOC 2027 submission, manuscript of 2026-11-03,
sha256 6d48ad24…, Lemma 6.1, p.20). Fix the data of Definition 2.1, a complete refined instrument
`Φ` (21) with entering memory `C^r`, and a unit vector `u ∈ C^r`; let `σ, δ_j` be as in (23), `H_σ`
the variance Hilbert space of (24) and `F*`, `ℓ_j` the maps of (25). Then
1. `F*` and every `ℓ_j` are well defined on `H_σ` (they factor through the quotient map);
2. (26) `‖F* X‖² + β⁻¹ Σ_j p_j ℓ_j(X)² ≤ ‖X‖²_σ` for every Hermitian recorded test `X`;
3. (28) `0 ⪯ C ⪯ βΔ`, `0 ⪯ Δ ⪯ I` and `rank F ≤ 2r − 2`, where `c_j` is the Riesz representer of
   `ℓ_j`, `F` the real adjoint of `F*`, `C = Σ_j p_j |c_j⟩⟨c_j|` and `Δ = I − F F*` (27).

**Formalization Note.** Operator inequalities on `H_σ` are `LinearMap.IsPositive` of differences;
`rank F` is the dimension of the range of `F`. `F*` takes values in real coordinates of `C^r`
(its values lie in `u^⊥`); this changes neither `‖F*X‖`, `F F*` nor `rank F`. -/
theorem lemma_6_1 {D M : ℕ} {G : Fin M → Matrix (Fin D) (Fin D) ℂ} {p : Fin M → ℝ}
    (hG : ProfileData G p) {ι : Type} [Fintype ι] {r K : ℕ} (Φ : FinInstrument ι r D K)
    (u : Fin r → ℂ) (hu : star u ⬝ᵥ u = 1) :
    (∀ X : hermTests Φ, FstarH Φ u (toHsig Φ u X) = FstarV Φ u X ∧
      ∀ j, ellH Φ u (G j) (toHsig Φ u X) = ellV Φ u (G j) X) ∧
    (∀ X : hermTests Φ, ‖FstarV Φ u X‖ ^ 2 +
      (1 / gramNorm G p) * ∑ j, p j * (ellV Φ u (G j) X) ^ 2 ≤ varSq Φ u (X : RecTest Φ)) ∧
    (Cop Φ u G p).IsPositive ∧ (gramNorm G p • Delta Φ u - Cop Φ u G p).IsPositive ∧
    (Delta Φ u).IsPositive ∧ (LinearMap.id - Delta Φ u).IsPositive ∧
    Module.finrank ℝ (LinearMap.range (Fmap Φ u)) ≤ 2 * r - 2 := by sorry

end PersistQMem
