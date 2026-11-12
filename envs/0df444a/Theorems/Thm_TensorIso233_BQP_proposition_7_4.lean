-- Prove2me | Theorems.Thm_TensorIso233_BQP_proposition_7_4
-- name    : TensorIso233.BQP.proposition_7_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T07:08:40.667748+00:00
-- url     : https://prove2.me/theorems/897427b3-afd6-46d2-8811-e84069c4dcda
-- title:
--   Proposition 7.4 — the quadratic-kernel criterion
-- statement:
--   Let $T,T'$ be in the quadratic-kernel case and let $(K_T,H_T)$, $(K_{T'},H_{T'})$ be any data as in Lemma 7.3 (either sign of the primitive kernel, any basis of the saturated output span). Then:
--
--   1. $|\det K_T|$ and $|\det H_T|$ are isomorphism invariants: $T\cong T'$ implies $|\det K_T|=|\det K_{T'}|$ and $|\det H_T|=|\det H_{T'}|$;
--   2. if both absolute determinants agree, then $T\cong T'$ if and only if some $S\in GL_2(\mathbb Z)$ satisfies
--   $$
--   H_{T'}SH_T^{-1}\in\mathrm{Mat}_2(\mathbb Z),\qquad K_{T'}\Sigma_2(S)K_T^{-1}\in\mathrm{Mat}_3(\mathbb Z),\tag{7.8}
--   $$
--   with $\Sigma_2(S)$ from (7.6).
--
--   The only remaining unknown is the first-factor matrix $S$.
--
--   Differences from the source:
--   - encoding: H_T′ S H_T⁻¹ ∈ Mat₂(ℤ) and K_T′ Σ₂(S) K_T⁻¹ ∈ Mat₃(ℤ) → ∃ integer X with X H_T = H_T′ S, and ∃ integer Y with Y K_T = K_T′ Σ₂(S); reason: H_T and K_T are invertible over ℚ (Lemma 7.3), so these are the same conditions without rational inverses
--   - reading: after comparing these invariants → under the hypotheses |det K_T| = |det K_T′| and |det H_T| = |det H_T′|; reason: the comparison rejects unless both agree; the criterion is asserted for the remaining pairs
-- source:
--   Thomas Huffstutler, Integral 2 × 3 × 3 Tensor Isomorphism is in BQP, STOC 2027 submission #319 (October 2026), Proposition 7.4, p. 37, (7.6)–(7.8); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/319.pdf

import Definitions.Def_TensorIso233_BQP_Pencil

namespace TensorIso233.BQP

/-- Proposition 7.4 (p. 37): in the quadratic-kernel case, for any admissible data
`(K_T, H_T)` and `(K_{T'}, H_{T'})`, the absolute determinants are isomorphism invariants, and
once they agree, `T ≅ T'` iff some `S ∈ GL₂(ℤ)` makes `H_{T'} S H_T⁻¹` and
`K_{T'} Σ₂(S) K_T⁻¹` integral (7.8). -/
theorem proposition_7_4 (T T' : Tensor) (hT : QuadKernelCase T) (hT' : QuadKernelCase T')
    (K K' : Mat3) (W W' : Matrix (Fin 3) (Fin 2) ℤ) (H H' : Matrix (Fin 2) (Fin 2) ℤ)
    (hadm : IsAdmissible T K W H) (hadm' : IsAdmissible T' K' W' H') :
    (Iso T T' → |K.det| = |K'.det| ∧ |H.det| = |H'.det|) ∧
    (|K.det| = |K'.det| → |H.det| = |H'.det| →
      (Iso T T' ↔ ∃ S : GL2,
        (∃ Xm : Matrix (Fin 2) (Fin 2) ℤ, Xm * H = H' * (S : Matrix (Fin 2) (Fin 2) ℤ)) ∧
        (∃ Ym : Mat3, Ym * K = K' * sigma2 (S : Matrix (Fin 2) (Fin 2) ℤ)))) := by sorry

end TensorIso233.BQP
