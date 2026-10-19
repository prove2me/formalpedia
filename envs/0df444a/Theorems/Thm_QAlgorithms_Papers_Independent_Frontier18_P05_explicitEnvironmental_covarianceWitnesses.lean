-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Frontier18_P05_explicitEnvironmental_covarianceWitnesses
-- name    : QAlgorithms.Papers.Independent.Frontier18.P05.explicitEnvironmental_covarianceWitnesses
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T08:49:52.008981+00:00
-- url     : https://prove2.me/theorems/f7b09099-446f-4bb1-9f71-fc64a13e7231
-- title:
--   Explicit pure and mixed environmental covariance witnesses
-- statement:
--   Let $n\ge1$, $X,Y\in\mathbb R^{2n\times2n}$, $\Sigma=\sigma_n-X^T\sigma_nX$, and assume $Y-i\Sigma\succeq0$. Here $\sigma_n=\begin{pmatrix}0&I_n\\-I_n&0\end{pmatrix}$. Put $P=\operatorname{proj}_{\operatorname{range}Y}$ and $\bar Y=Y+I-P$. There exist a symmetric positive definite $R$, an orthogonal $O$, and numbers $\mu_j\in[0,1]$ such that $R^2=\bar Y$ and
--
--   $$OR^{-1}\Sigma R^{-T}O^T=\begin{pmatrix}0&\operatorname{diag}\mu\\-\operatorname{diag}\mu&0\end{pmatrix},\qquad P\bar YP=Y.$$
--
--   For each $j$, put $a_j=1$ if $\mu_j=0$ and $a_j=\sqrt{\mu_j}$ otherwise; put $d_j=5/4$ if $\mu_j=0$ and $d_j=\mu_j^{-1}$ otherwise. Write $D=\operatorname{diag}(d,d)$, $F=\begin{pmatrix}0&\operatorname{diag}f(d)\\\operatorname{diag}f(d)&0\end{pmatrix}$, where $f(t)=-\sqrt{t^2-1}$. Let $A=\begin{pmatrix}0&P_0\\P_0&0\end{pmatrix}$, where $P_0=\operatorname{diag}(\mathbf1_{\mu_j=0})$. Define
--
--   $$G=\begin{pmatrix}D&F\\F^T&D\end{pmatrix},\qquad B=PRO^T[\operatorname{diag}(a,a),A].$$
--
--   Then $G$ is physical and pure relative to $\sigma_n\oplus\sigma_n$, $B(\sigma_n\oplus\sigma_n)B^T=\Sigma$, and $BGB^T=Y$. To obtain the reduced pure construction, retain all first-block modes and only second-block modes with $\mu_j\ne1$. To obtain the mixed construction, retain all first-block modes and only second-block modes with $\mu_j=0$. In each case restrict $G$ to those rows and columns and $B$ to those columns. The restricted covariance is physical and obeys the same two coupling identities; the first is pure. If $L_p,L_m$ are their total mode counts, then
--
--   $$2L_p=4n-r',\qquad 2L_m+r=4n,$$
--
--   where $r=\operatorname{rank}\Sigma$, $r'=\operatorname{rank}Y-\operatorname{rank}(Y-\Sigma Y^+\Sigma^T)$, and $Y^+=P\bar Y^{-1}P$. The pure construction consists of unpaired vacuum modes, purified nonvacuum thermal modes and null-mode entangled pairs; the mixed construction drops the nonvacuum thermal purifiers. These formulas cover the singular case by the left factor $P$ and specify the Appendix C matrices up to simultaneous mode ordering.
--
--   **Formalization Note** The final sentence after Eq.(133) prints $r$ added modes for $r/2$ thermal modes; the consistent count is $r/2$.
-- source:
--   Multi-mode bosonic Gaussian channels, arXiv:0804.0511v3, PDF p. 32, Appendices B–C: Explicit physical pure/mixed environmental witnesses

import Definitions.Def_QAlgorithms_Papers_Independent_Frontier18_P05

noncomputable section

open scoped ComplexOrder

namespace QAlgorithms.Papers.Independent.Frontier18.P05

open QAlgorithms.Papers.Independent.Dependency50.P10

/-- Explicit witnesses, PDF pp.12–13, Eqs.(34),(41)–(53), and Appendices B–C,
PDF pp.30–33, Eqs.(122)–(133). All matrices are constructed from X,Y via an
existentially obtained positive square root R, orthogonal O, and skew spectrum mu.
The base covariance is the accepted thermal purification with f(d)=-sqrt(d^2-1).
Taking the indicated principal submatrices implements all the rectangular reduced
constructions (126)–(133), up to simultaneous mode reordering.

Source correction: the final sentence after Eq.(133), PDF p.33, prints r added
modes to purify r/2 thermal modes. The construction uses r/2, giving 2n total.
No operational all-input Fock channel identity is asserted by this matrix result. -/
theorem explicitEnvironmental_covarianceWitnesses {n : ℕ} (hn : 0 < n)
    (X Y : Matrix (Phase n) (Phase n) ℝ) (hCP : (cpMatrix X Y).PosSemidef) :
    let P := realRangeProjection Y
    let Ybar := Y + (1 - P)
    ∃ R O : Matrix (Phase n) (Phase n) ℝ,
      ∃ mu : Fin n → ℝ,
        R.transpose = R ∧ R.PosDef ∧ R * R = Ybar ∧
        O * O.transpose = 1 ∧
        (∀ j, 0 ≤ mu j ∧ mu j ≤ 1) ∧
        O * R⁻¹ * commutatorDefect X * (R⁻¹).transpose * O.transpose =
          normalizedDefect mu ∧
        P * Ybar * P = Y ∧
        (let B := P * R * O.transpose * fullCoupling mu
         let G := thermalPurification (fun j => environmentVariance (mu j))
         pureCovariance G (jointSigma n n) ∧
         B * jointSigma n n * B.transpose = commutatorDefect X ∧
         B * G * B.transpose = Y ∧
         ∀ pure : Bool,
           let q := retainedCount mu pure
           let e := retainedEmbedding mu pure
           let Bsmall := B.submatrix id e
           let Gsmall := G.submatrix e e
           physicalCovariance Gsmall (jointSigma n q) ∧
           (pure = true → pureCovariance Gsmall (jointSigma n q)) ∧
           Bsmall * jointSigma n q * Bsmall.transpose = commutatorDefect X ∧
           Bsmall * Gsmall * Bsmall.transpose = Y ∧
           (pure = true →
             (2 : ℤ) * ((n + q : ℕ) : ℤ) = (4 : ℤ) * (n : ℤ) -
               ((Y.rank : ℤ) - ((rankResidual Y (commutatorDefect X)).rank : ℤ))) ∧
           (pure = false →
             2 * (n + q) + (commutatorDefect X).rank = 4 * n)) := by sorry

end QAlgorithms.Papers.Independent.Frontier18.P05

end
