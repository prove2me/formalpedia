-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P98_completelyBoundedNorms_sdp
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P98.completelyBoundedNorms_sdp
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T08:53:44.554564+00:00
-- url     : https://prove2.me/theorems/6c6cdd39-3201-4569-87f5-a001d93ee760
-- title:
--   Explicit SDPs for completely bounded norms
-- statement:
--   Let $X=\mathbb C^n$ and $Y=\mathbb C^m$, where $n,m\ge1$, and let $\Phi:L(X)\to L(Y)$ be complex-linear. Suppose $A,B:X\to Y\otimes Z$ satisfy $\Phi(T)=\operatorname{Tr}_Z(ATB^*)$ for every operator $T$, with $\dim Z=\operatorname{rank}J(\Phi)$. For the output-first, unnormalized Choi matrix $J$, construct
--   $$
--   \Psi\begin{pmatrix}T&M\\N&W\end{pmatrix}=\begin{pmatrix}\operatorname{Tr}T&0\\0&\operatorname{Tr}_Y(W-ATA^*)\end{pmatrix},\quad C=\operatorname{diag}(0,BB^*),\quad D=\operatorname{diag}(1,0).
--   $$
--   Let $\alpha$ be the supremum of $\operatorname{Re}\operatorname{Tr}(C^*P)$ over $P\succeq0$ with $\Psi(P)\preceq D$, and let $\beta$ be the infimum of $\operatorname{Re}\operatorname{Tr}(D^*S)$ over $S\succeq0$ with $\Psi^*(S)\succeq C$. Then
--   $$
--   \alpha=\beta=\|\Phi\|_\diamond^2.
--   $$
--   A minimal Stinespring pair exists for the Hilbert–Schmidt adjoint $\Phi^*$, and this same construction applied to it has primal and dual values $\|\Phi\|_{\mathrm{cb},\infty}^2=\|\Phi^*\|_\diamond^2$. Trace norm has no factor $1/2$. At the zero map the minimal environment is allowed to have dimension zero.
--
--   These explicit programs express both completely bounded norms by finite-dimensional semidefinite optimization; the computational complexity claim is inventoried separately.
-- source:
--   Semidefinite programs for completely bounded norms, arXiv:0901.4709v2, PDF p. 7, Abstract and §3: explicit SDPs for completely bounded trace and spectral norms

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P98

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

namespace QAlgorithms.Papers.Independent.Intakenext100.P98

/-- PDF pp.1,4,7--9: explicit SDP values are the SQUARED diamond norm.
Applying the construction to the adjoint gives the spectral variant.
Phi need not be positive, Hermiticity-preserving, or nonzero. -/
theorem completelyBoundedNorms_sdp {n m r : ℕ} (hn : 0 < n) (hm : 0 < m)
    (Phi : (Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin m) (Fin m) ℂ)) (A B : (Matrix (Fin m × Fin r) (Fin n) ℂ))
    (hpair : stinespringPairRepresents Phi A B) (hminimal : r = (watrousChoiMatrix Phi).rank) :
    blockPrimalValue A B = (((stabilizedTraceNorm Phi) ^ 2 : ℝ) : EReal) ∧
    blockDualValue A B = (((stabilizedTraceNorm Phi) ^ 2 : ℝ) : EReal) ∧
    ∃ (s : ℕ) (C D : (Matrix (Fin n × Fin s) (Fin m) ℂ)),
      stinespringPairRepresents (superAdjoint Phi) C D ∧ s = (watrousChoiMatrix (superAdjoint Phi)).rank ∧
      blockPrimalValue C D = (((cbSpectral Phi) ^ 2 : ℝ) : EReal) ∧
      blockDualValue C D = (((cbSpectral Phi) ^ 2 : ℝ) : EReal) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P98

end
