-- Prove2me | Theorems.Thm_QAlgorithms_Papers_RoadmapX02_negativity_convex
-- name    : QAlgorithms.Papers.RoadmapX02.negativity_convex
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-18T19:46:39.154437+00:00
-- url     : https://prove2.me/theorems/3b0c0828-1dfc-4b38-813a-2b087e945239
-- title:
--   Convexity of negativity for Hermitian bipartite matrices
-- statement:
--   Let $d_A,d_B$ be positive integers, and fix an orthonormal product basis of $\mathbb C^{d_A}\otimes\mathbb C^{d_B}$. For a matrix $M$ on this space, let $M^{T_A}$ denote its partial transpose on the first subsystem, so that $(M^{T_A})_{(a,b),(c,e)}=M_{(c,b),(a,e)}$. Write $\|X\|_1=\operatorname{tr}\sqrt{X^\dagger X}$ and $\mathcal N(M)=(\|M^{T_A}\|_1-1)/2$. Let $\rho_1,\ldots,\rho_r$ be any finite family of Hermitian matrices on this space, and let $p_1,\ldots,p_r$ be nonnegative real numbers with $\sum_{i=1}^r p_i=1$. Then
--
--   $$
--   \mathcal N\!\left(\sum_{i=1}^r p_i\rho_i\right)\le\sum_{i=1}^r p_i\mathcal N(\rho_i).
--   $$
--
--   This expresses convexity of negativity under mixing, a property used in the paper's subsequent study of entanglement monotonicity. As in the printed proposition and its proof, the matrices need not be positive or have trace one; the displayed definition therefore gives $\mathcal N(0)=-1/2$ outside the state domain.
-- source:
--   A computable measure of entanglement, arXiv:quant-ph/0102117v1, §II.A, Proposition 1, Eq. (7), PDF p. 2. https://arxiv.org/abs/quant-ph/0102117v1 . PDF SHA-256: a6bc5031b04d93cf18e71e39425eea8b9b8c938252bb87d8067d890269b90f7b.

import Definitions.Def_QAlgorithms_Defs_EntanglementNegativity
set_option autoImplicit false

namespace QAlgorithms.Papers.RoadmapX02

/-- Vidal and Werner, *A computable measure of entanglement*,
arXiv:quant-ph/0102117v1, PDF p.2, Section II.A, Proposition 1, Eq. (7).
Negativity is convex for every finite family of Hermitian bipartite matrices
and nonnegative real weights summing to one. The local dimensions are positive.
The source's formula is `(traceNorm (partialTransposeFirst M) - 1) / 2`
(Eq. (1), PDF p.1, and Proposition 1's proof, PDF p.2), even for matrices
that are not positive or trace-one; in particular its value at zero is -1/2.
Partial transpose acts on Alice's first factor in the fixed product basis,
as in Eq. (3), PDF p.2. -/
theorem negativity_convex {dA dB count : ℕ} (hA : 0 < dA) (hB : 0 < dB)
    (rho : Fin count → Matrix (Fin dA × Fin dB) (Fin dA × Fin dB) ℂ)
    (hermitian : ∀ i, (rho i).IsHermitian)
    (p : Fin count → ℝ) (nonnegative : ∀ i, 0 ≤ p i) (total : ∑ i, p i = 1) :
    QAlgorithms.Entanglement.negativity (∑ i, (p i : ℂ) • rho i) ≤
      ∑ i, p i * QAlgorithms.Entanglement.negativity (rho i) := by sorry

end QAlgorithms.Papers.RoadmapX02
