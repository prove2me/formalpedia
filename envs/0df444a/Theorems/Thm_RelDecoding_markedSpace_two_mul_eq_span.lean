-- Prove2me | Theorems.Thm_RelDecoding_markedSpace_two_mul_eq_span
-- name    : RelDecoding.markedSpace_two_mul_eq_span
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T06:23:25.031387+00:00
-- url     : https://prove2.me/theorems/aba10ba9-6787-4f46-84f9-46c0aababcab
-- title:
--   $\mathcal F^A_{2D}=\operatorname{span}\{X^*Y:X,Y\in\mathcal F^A_D\}$
-- statement:
--   Let $a_1,\dots,a_s$ be complex square matrices, $\mathcal A=C^*(I_A,a_1,\dots,a_s)$, and $\mathcal F^A_t$ the span of the identity and the marked words of length at most $t$ in the $a_i$ and their adjoints. Then for every integer $D\ge0$,
--
--   $$\mathcal F^A_{2D}=\operatorname{span}\{X^*Y:\ X,Y\in\mathcal F^A_D\}.$$
--
--   This identity drives the converse direction of Proposition 4.2: trace matching on all products $X^*Y$ of degree-$D$ elements gives trace matching on the whole degree-$2D$ space.
--
--   Differences from the source:
--   - encoding: marked words a_{i₁}^{ϵ₁}⋯a_{i_ℓ}^{ϵ_ℓ}, ϵⱼ ∈ {1, ∗}, empty word = I_A; 𝓕ᴬ_t their span for ℓ ≤ t → words are List (Fin s × Bool) with true = adjoint, evaluated by wordEval; 𝓕ᴬ_t = markedSpace a t, a Submodule ℂ of A; reason: Lean convention; same spaces
-- source:
--   Shang, Stilck França, From Simple Sources to Quantum Advantage: Homomorphic Polynomial Transduction via Relative Decoding, arXiv:2609.35101 (held version, sha256 d2be7859…), proof of Proposition 4.2, p.18 (pdf_page 18)

import Mathlib
import Definitions.Def_RelDecoding_markedSpace

set_option autoImplicit false

namespace RelDecoding

/-- **Span identity in the proof of Proposition 4.2.** For every integer `D ≥ 0`,
`𝓕ᴬ_{2D} = span{X∗Y : X, Y ∈ 𝓕ᴬ_D}`. Shang, Stilck França, *From Simple Sources to Quantum
Advantage: Homomorphic Polynomial Transduction via Relative Decoding*, arXiv:2609.35101 (held
version, sha256 d2be7859…), proof of Proposition 4.2, p.18.

**Formalization Note.** Both sides are complex subspaces of `A = C∗(I_A, a)`; the equality is an
equality of `Submodule`s. -/
theorem markedSpace_two_mul_eq_span {nA : Type*} [Fintype nA] [DecidableEq nA] {s : ℕ}
    (a : Fin s → Matrix nA nA ℂ) (D : ℕ) :
    markedSpace a (2 * D) = Submodule.span ℂ
      {Z | ∃ X ∈ markedSpace a D, ∃ Y ∈ markedSpace a D, Z = star X * Y} := by sorry

end RelDecoding
