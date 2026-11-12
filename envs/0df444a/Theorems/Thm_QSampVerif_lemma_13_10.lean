-- Prove2me | Theorems.Thm_QSampVerif_lemma_13_10
-- name    : QSampVerif.lemma_13_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-11T08:28:25.224602+00:00
-- url     : https://prove2.me/theorems/ad36bb16-70c5-4ae8-859b-796da6f16199
-- title:
--   Lemma 13.10 — vector polarization $|a\rangle\langle b|=\sum_{z\in\mathcal Z}z\,|u_z\rangle\langle u_z|$
-- statement:
--   Let $a,b$ be vectors in a finite-dimensional complex inner-product space with $\|a\|,\|b\|\le1$, and let $u_z=(a+zb)/2$ for $z\in\mathcal Z=\{1,i,-1,-i\}$. Then
--
--   $$|a\rangle\langle b|=\sum_{z\in\mathcal Z}z\,|u_z\rangle\langle u_z|,\qquad(476)$$
--
--   and $\|u_z\|\le1$ for every $z\in\mathcal Z$.
--
--   This writes a cross term as a combination of four positive rank-one operators built from vectors of norm at most one, which is how the soundness bound for positive inputs is extended to cross terms (Lemma 13.12).
--
--   Differences from the source:
--   - encoding: |a⟩⟨b|; 𝒵 → the matrix vecMulVec a (conj b); z ranging over i^k, k ∈ Fin 4; reason: same objects
-- source:
--   Chung, Cojocaru, Lee, Lin, Classical Verification of Quantum Sampling with Negligible Error, STOC 2027 submission (held version, sha256 dbc19d8f…7ee7), Lemma 13.10, (476), p.178 (PDF 179)

import Definitions.Def_QSampVerif_zPhase

set_option autoImplicit false

namespace QSampVerif

/-- Chung, Cojocaru, Lee, Lin, STOC 2027 submission (held version, sha256 dbc19d8f…7ee7),
Lemma 13.10 (Vector polarization), (476), p.178 (PDF 179).

For vectors `a, b` with `‖a‖, ‖b‖ ≤ 1` and `u_z = (a + z b)/2`,
`|a⟩⟨b| = Σ_{z ∈ Z} z |u_z⟩⟨u_z|`, and `‖u_z‖ ≤ 1` for every `z ∈ Z = {1, i, −1, −i}`.

**Formalization Note.** `|a⟩⟨b|` is the matrix `vecMulVec a (star b)`; `Z` is enumerated as
`zPhase k = i^k`. -/
theorem lemma_13_10 {ι : Type*} [Fintype ι] (a b : EuclideanSpace ℂ ι) (ha : ‖a‖ ≤ 1)
    (hb : ‖b‖ ≤ 1) :
    Matrix.vecMulVec (WithLp.ofLp a) (star (WithLp.ofLp b)) =
      ∑ k : Fin 4, zPhase k • Matrix.vecMulVec (WithLp.ofLp ((2⁻¹ : ℂ) • (a + zPhase k • b)))
        (star (WithLp.ofLp ((2⁻¹ : ℂ) • (a + zPhase k • b)))) ∧
    ∀ k : Fin 4, ‖(2⁻¹ : ℂ) • (a + zPhase k • b)‖ ≤ 1 := by sorry

end QSampVerif
