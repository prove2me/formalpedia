-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P44_commonGramCompression
-- name    : QAlgorithms.Papers.Independent.Information100.P44.commonGramCompression
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T11:48:38.656909+00:00
-- url     : https://prove2.me/theorems/3f0dad12-014c-4751-aede-f96e7a47d220
-- title:
--   VI B: common Choi-sector compression is positive
-- statement:
--   Let $G_{\rm glob}\succeq0$ be a finite complex Gram matrix, let $R,S:\mathbb C^g\to\mathbb C^h$ be fixed injective linear selectors, and let $z\in\mathbb C^h$ select a scalar direction. Define $A=R^\dagger G_{\rm glob}R$, $B=S^\dagger G_{\rm glob}S$, $F=R^\dagger G_{\rm glob}S$, $D=R^\dagger G_{\rm glob}z$, $E=S^\dagger G_{\rm glob}z$, and $c=z^\dagger G_{\rm glob}z$. With $T=[R\ S\ z]$,
--   $$\begin{pmatrix}A&F&D\\F^\dagger&B&E\\D^\dagger&E^\dagger&c\end{pmatrix}=T^\dagger G_{\rm glob}T\succeq0.$$
--   All blocks come from this single global object. The abstract selectors are not assigned unspecified physical coordinates, and no rank-one conclusion is asserted.
-- source:
--   Limitations on Joint Coherence Transfer in Quantum Thermodynamics, arXiv:2608.11872v1, PDF p. 21, VI B: common Choi-sector compression is positive

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P44

namespace QAlgorithms.Papers.Independent.Information100.P44

noncomputable section

open scoped ComplexConjugate ComplexOrder Matrix

attribute [local instance] Classical.propDecidable

/-- PDF p.21, VI B: all blocks are computed from one positive global Gram object. -/
theorem commonGramCompression {h g : ℕ} (G : Mat h) (hG : G.PosSemidef)
    (R S : Matrix (Fin h) (Fin g) ℂ) (z : Fin h → ℂ)
    (hR : Function.Injective R.mulVec) (hS : Function.Injective S.mulVec) :
    let A := Rᴴ * G * R
    let B := Sᴴ * G * S
    let F := Rᴴ * G * S
    let D := (Rᴴ * G).mulVec z
    let E := (Sᴴ * G).mulVec z
    let c := ∑ i, conj (z i) * (G.mulVec z) i
    ladderGram A B F D E c = (gramSelector R S z)ᴴ * G * gramSelector R S z ∧
      (ladderGram A B F D E c).PosSemidef := by sorry

end

end QAlgorithms.Papers.Independent.Information100.P44
