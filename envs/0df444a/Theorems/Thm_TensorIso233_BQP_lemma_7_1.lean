-- Prove2me | Theorems.Thm_TensorIso233_BQP_lemma_7_1
-- name    : TensorIso233.BQP.lemma_7_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T07:08:34.080609+00:00
-- url     : https://prove2.me/theorems/395edba3-ac1e-4118-af91-3e74c5295ca3
-- title:
--   Lemma 7.1 — the marked diagram criterion
-- statement:
--   Consider pencils of the form (7.1),
--   $$
--   M_T(z)=\begin{pmatrix}\ell_Tz&(R_Tz)^{\mathsf T}\\C_Tz&0_{2\times2}\end{pmatrix},\qquad z=(x,y)^{\mathsf T},
--   $$
--   with $\ell_T\in\mathrm{Mat}_{1\times2}(\mathbb Z)$, $C_T,R_T\in\mathrm{Mat}_2(\mathbb Z)$, $R_T$ nonsingular and $C_T\neq0$, and similarly for $T'$. Let $X_T=(\ell_T;C_T;R_T):\mathbb Z^2\to\mathbb Z^5$, $\Lambda_1=\mathbb Z\oplus\mathbb Z^2\oplus0$ and $\Lambda_2=\mathbb Z\oplus0\oplus\mathbb Z^2$. The two tensors are integrally isomorphic (2.1) if and only if there are $S\in GL_2(\mathbb Z)$ and $F\in GL_5(\mathbb Z)$ with
--
--   $$
--   FX_T=X_{T'}S,\qquad F\Lambda_1=\Lambda_1,\qquad F\Lambda_2=\Lambda_2 .\tag{7.2}
--   $$
--
--   The sublattice conditions force $F$ to preserve the decomposition of $\mathbb Z^5$ into the $\ell_T$, $C_T$ and $R_T$ coordinates. This turns the linear-kernel case into a lattice-isomorphism problem for a diagram.
--
--   Differences from the source:
--   - encoding: pencils M_T(z) = xA − yB of the form (7.1); integrally tensor-isomorphic → the tensor pencil71 ℓ C R whose slices are the x- and (−y)-coefficients of (7.1); Iso under (2.1); reason: M_T = xA − yB determines (A, B); the pencil form P M_T(z) = M_T′(Sz)Q is equivalent to (2.1)
--   - encoding: F Λᵢ = Λᵢ → the image of Λᵢ under the ℤ-linear map of F equals Λᵢ; reason: literal
-- source:
--   Thomas Huffstutler, Integral 2 × 3 × 3 Tensor Isomorphism is in BQP, STOC 2027 submission #319 (October 2026), Lemma 7.1, p. 31, (7.1)–(7.2), p. 30; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/319.pdf

import Definitions.Def_TensorIso233_BQP_Pencil

namespace TensorIso233.BQP

/-- Lemma 7.1 (p. 31): two pencils of the form (7.1) (with `R_T` nonsingular and `C_T ≠ 0`) are
integrally tensor-isomorphic iff there are `S ∈ GL₂(ℤ)` and `F ∈ GL₅(ℤ)` with
`F X_T = X_{T'} S`, `F Λ₁ = Λ₁` and `F Λ₂ = Λ₂` (7.2). -/
theorem lemma_7_1 (ℓ ℓ' : Matrix (Fin 1) (Fin 2) ℤ) (Cm Cm' R R' : Matrix (Fin 2) (Fin 2) ℤ)
    (hR : R.det ≠ 0) (hR' : R'.det ≠ 0) (hC : Cm ≠ 0) (hC' : Cm' ≠ 0) :
    Iso (pencil71 ℓ Cm R) (pencil71 ℓ' Cm' R') ↔
      ∃ (S : GL2) (F : GL5),
        (F : Matrix (Fin 5) (Fin 5) ℤ) * markedX ℓ Cm R =
            markedX ℓ' Cm' R' * (S : Matrix (Fin 2) (Fin 2) ℤ) ∧
          Lambda1.map (Matrix.toLin' (F : Matrix (Fin 5) (Fin 5) ℤ)) = Lambda1 ∧
          Lambda2.map (Matrix.toLin' (F : Matrix (Fin 5) (Fin 5) ℤ)) = Lambda2 := by sorry

end TensorIso233.BQP
