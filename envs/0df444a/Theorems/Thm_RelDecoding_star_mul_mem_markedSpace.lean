-- Prove2me | Theorems.Thm_RelDecoding_star_mul_mem_markedSpace
-- name    : RelDecoding.star_mul_mem_markedSpace
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T06:23:13.978986+00:00
-- url     : https://prove2.me/theorems/d9952c62-cc65-46e6-a25d-25f1f02ed492
-- title:
--   $X^*Y\in\mathcal F^A_{2D}$ for $X,Y\in\mathcal F^A_D$
-- statement:
--   Let $a_1,\dots,a_s$ be complex square matrices, $\mathcal A=C^*(I_A,a_1,\dots,a_s)$, and $\mathcal F^A_t$ the span of the identity and the marked words of length at most $t$ in the $a_i$ and their adjoints. Then for every integer $D\ge0$,
--
--   $$X,Y\in\mathcal F^A_D\ \Longrightarrow\ X^*Y\in\mathcal F^A_{2D}.$$
--
--   This is the first step of the forward direction of Proposition 4.2: products $X^*Y$ of degree-$D$ elements stay in degree $2D$, where the relative distance controls the traces.
--
--   Differences from the source:
--   - encoding: marked words a_{i₁}^{ϵ₁}⋯a_{i_ℓ}^{ϵ_ℓ}, ϵⱼ ∈ {1, ∗}, empty word = I_A; 𝓕ᴬ_t their span for ℓ ≤ t → words are List (Fin s × Bool) with true = adjoint, evaluated by wordEval; 𝓕ᴬ_t = markedSpace a t, a Submodule ℂ of A; reason: Lean convention; same spaces
-- source:
--   Shang, Stilck França, From Simple Sources to Quantum Advantage: Homomorphic Polynomial Transduction via Relative Decoding, arXiv:2609.35101 (held version, sha256 d2be7859…), proof of Proposition 4.2, p.18 (pdf_page 18)

import Mathlib
import Definitions.Def_RelDecoding_markedSpace

set_option autoImplicit false

namespace RelDecoding

/-- **Forward step of Proposition 4.2: `X∗Y ∈ 𝓕ᴬ_{2D}`.** For every integer `D ≥ 0` and all
`X, Y ∈ 𝓕ᴬ_D`, the product `X∗Y` lies in `𝓕ᴬ_{2D}`. Shang, Stilck França, *From Simple Sources
to Quantum Advantage: Homomorphic Polynomial Transduction via Relative Decoding*,
arXiv:2609.35101 (held version, sha256 d2be7859…), proof of Proposition 4.2, p.18.

**Formalization Note.** `𝓕ᴬ_t` is the complex span, inside `A = C∗(I_A, a)`, of the values of
marked words of length at most `t` (eq. (43)); `X∗` is the adjoint in `A`. -/
theorem star_mul_mem_markedSpace {nA : Type*} [Fintype nA] [DecidableEq nA] {s : ℕ}
    (a : Fin s → Matrix nA nA ℂ) (D : ℕ) {X Y : genAlg a}
    (hX : X ∈ markedSpace a D) (hY : Y ∈ markedSpace a D) :
    star X * Y ∈ markedSpace a (2 * D) := by sorry

end RelDecoding
