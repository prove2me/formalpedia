-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P37_unitalChannelMoments
-- name    : QAlgorithms.Papers.Independent.Information100.P37.unitalChannelMoments
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T11:17:13.053724+00:00
-- url     : https://prove2.me/theorems/401a82cc-4fd9-4e81-9fc7-baf704e34854
-- title:
--   Theorem 17, CGPD for unital channels
-- statement:
--   Fix a reference orthonormal basis of a finite-dimensional complex Hilbert space of dimension $d\ge1$. For a population vector $p$ in the closed simplex $\{p_i\ge0,\ \sum_i p_i=1\}$, let $\rho_p=\operatorname{diag}p$. The input law $\nu_d=\operatorname{Dir}(1,\ldots,1)$ is uniform on this whole simplex. Write $c_B(\rho)=\sum_{i\ne j}|\rho_{ij}|^2$ for squared Hilbert–Schmidt coherence. For a fixed unitary $U$, set $X_U(p)=c_B(U\rho_pU^\dagger)$, $C_U=\mathbb E_{\nu_d}X_U$, $\Delta_U=\sqrt{\operatorname{Var}_{\nu_d}X_U}$, $P_{ij}=|U_{ij}|^2$, $G=I-P^TP$, $H_d=I-\mathbf1\mathbf1^T/d$, and $D_d=d(d+1)(d+2)(d+3)$. For a channel $\mathcal E$, replace $X_U$ by $X_{\mathcal E}(p)=c_B(\mathcal E(\rho_p))$, with its own mean $C_{\mathcal E}$ and deviation $\Delta_{\mathcal E}$. A channel is completely positive and trace preserving; unitality, where specified, means $\mathcal E(I)=I$.
--
--   Assume $d\ge2$ and let $\mathcal E$ be CPTP and unital. Define $A_i=Q_B\mathcal E(|i\rangle\langle i|)$ and $G_{ij}=\operatorname{Re}\operatorname{Tr}(A_iA_j)$. Put $\gamma_d=2d/\sqrt{(d-1)(d+2)(d+3)}$, $A=G-\operatorname{Tr}(G)H_d/(d-1)$, and $\Xi_{\mathcal E}^2=(2\|A\|_F^2+6\|\operatorname{diag}A\|_2^2)/D_d$. All five formulas hold:
--   $$\begin{aligned} C_{\mathcal E}&=\frac{\operatorname{Tr}G}{d(d+1)},\\M_2(\mathcal E)&=\frac{(\operatorname{Tr}G)^2+2\operatorname{Tr}(G^2)+6\sum_iG_{ii}^2}{D_d},\\\Delta_{\mathcal E}^2&=M_2(\mathcal E)-\frac{(\operatorname{Tr}G)^2}{d^2(d+1)^2},\\\Delta_{\mathcal E}&\ge\gamma_d C_{\mathcal E},\\\Delta_{\mathcal E}^2&=\gamma_d^2 C_{\mathcal E}^2+\Xi_{\mathcal E}^2.\end{aligned}$$
--
--   The exact moment theory and fluctuation floor extend to unital channels.
-- source:
--   Coherence -generating power deviation: Fluctuations and input selectivity beyond average coherence generation, arXiv:2609.19046v1, PDF p. 9, Theorem 17, CGPD for unital channels

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P37

noncomputable section

namespace QAlgorithms.Papers.Independent.Information100.P37

open MeasureTheory ProbabilityTheory Filter

open scoped BigOperators Matrix ComplexConjugate Topology

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- PDF p.9, Theorem 17: all five referenced moment, variance and fluctuation formulas. -/
theorem unitalChannelMoments (hd : 2 ≤ Fintype.card ι) (E : Superop ι ι)
    (hE : IsChannel E) (hu : E 1 = 1) :
    let d := (Fintype.card ι : ℝ)
    let G := channelResponse E
    cgp E = G.trace / (d * (d + 1)) ∧
    moment E 2 = (G.trace ^ 2 + 2 * (G * G).trace + 6 * diagonalSq G) /
      fourthDenominator (Fintype.card ι) ∧
    cgpd E ^ 2 = (G.trace ^ 2 + 2 * (G * G).trace + 6 * diagonalSq G) /
      fourthDenominator (Fintype.card ι) - G.trace ^ 2 / (d ^ 2 * (d + 1) ^ 2) ∧
    gammaFactor (Fintype.card ι) * cgp E ≤ cgpd E ∧
    cgpd E ^ 2 = gammaFactor (Fintype.card ι) ^ 2 * cgp E ^ 2 + excess G ^ 2 := by sorry

end QAlgorithms.Papers.Independent.Information100.P37

end
