-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P50_remark_A_2
-- name    : QAlgorithms.Papers.Independent.Information100.P50.remark_A_2
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T12:11:27.828373+00:00
-- url     : https://prove2.me/theorems/76ead3e4-5654-48a4-a7e1-905c46562acc
-- title:
--   Remark A.2: For trace-preserving channels Phi,Psi, norm_(1→1)(Omega)=specNorm(Omega^*(I_Y))=2, and diamond(Phi sigma Psi)≤
-- statement:
--   All spaces are finite-dimensional complex Euclidean spaces. Input and output dimensions are positive wherever states or extreme eigenvalues occur. The Choi matrix $J$ is unnormalized and has output factor first. Write $\|\Theta\|_\diamond$ for the full completely bounded trace norm, $\|A\|_\infty$ for the operator norm, and $\Theta^*$ for the Hilbert–Schmidt adjoint.
--
--   For a fixed linearly independent Kraus family $(V_k)_{k=1}^r$, put $\Omega(X)=\sum_k V_kXV_k^*$, $W=[\operatorname{vec}(V_1)\ \cdots\ \operatorname{vec}(V_r)]$, and $\Psi_T(X)=\sum_{k,l}T_{kl}V_kXV_l^*$. An effect $T$ determines the pair $(\Psi_T,\Psi_{I-T})$ with common sum $\Omega$. This parametrizes exactly the source's pairs and derivatives, by the ARN correspondence. All derivatives compared use this same family.
--
--   A Kubo–Ando mean $\sigma$ has a nonnegative operator-monotone representing function $f_\sigma$ with $f_\sigma(1)=1$. Set $g_\sigma(t)=t f_\sigma((1-t)/t)$ for $0<t<1$, $g_\sigma(0)=f_\sigma'(\infty)$, and $g_\sigma(1)=f_\sigma(0+)$. Matrix functions use spectral functional calculus and singular means use decreasing positive regularization.
--
--   If $\Psi_T$ and $\Psi_{I-T}$ are channels, then
--
--   $$\|\Omega\|_{1\to1}=\|\Omega^*(I_Y)\|_\infty=2,\qquad \|\Psi_T\sigma\Psi_{I-T}\|_\diamond\le2\|g_\sigma(T)\|_\infty.$$
--
--   One cannot generally substitute $g_\sigma(\|T\|_\infty)$ for $\|g_\sigma(T)\|_\infty$: for $D=\operatorname{diag}(1/2,1)$ and $g_\#(t)=\sqrt{t(1-t)}$,
--
--   $$\|D\|_\infty=1,\quad\|g_\#(D)\|_\infty=1/2,\quad g_\#(\|D\|_\infty)=0.$$
--
--   This records the channel normalization and the failure of the proposed scalar substitution.
-- source:
--   Quantitative upper bounds for certain quantum channel divergences, arXiv:2610.16270v1, PDF p. 26, Remark A.2

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P50

noncomputable section

open scoped Matrix ComplexConjugate ENNReal Topology ComplexOrder Kronecker

open Filter Set

namespace QAlgorithms.Papers.Independent.Information100.P50

/-- Remark A.2, source PDF p.26. The final clause is the explicit counterexample to
substituting g_hash(norm T) for norm(g_hash(T)); it does not assert channel sharpness. -/
theorem remark_A_2 {dx dy r : ℕ} (hdx : 0 < dx) (hdy : 0 < dy)
    (s : Mean) (V : Fin r → Matrix (Fin dy) (Fin dx) ℂ) (hV : LinearIndependent ℂ V)
    (T : M r) (hT : IsEffect T)
    (hPhi : IsChannel (arnFamily V T)) (hPsi : IsChannel (arnFamily V (1 - T))) :
    inducedNorm 1 (krausMap V) = 2 ∧ specNorm (hilbertSchmidtAdjoint (krausMap V) 1) = 2 ∧
    cbTraceNorm (cpMean s (arnFamily V T) (arnFamily V (1 - T))) ≤
      2 * specNorm (cfc (meanPerspective s) T) ∧
    (let D : M 2 := Matrix.diagonal ![(1 / 2 : ℂ), 1]
     IsEffect D ∧ specNorm D = 1 ∧ specNorm (cfc gHash D) = 1 / 2 ∧ gHash (specNorm D) = 0) := by sorry

end QAlgorithms.Papers.Independent.Information100.P50

end
