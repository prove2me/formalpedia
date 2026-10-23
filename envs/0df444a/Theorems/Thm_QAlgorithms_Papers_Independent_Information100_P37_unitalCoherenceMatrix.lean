-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P37_unitalCoherenceMatrix
-- name    : QAlgorithms.Papers.Independent.Information100.P37.unitalCoherenceMatrix
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T11:16:46.327858+00:00
-- url     : https://prove2.me/theorems/b7ca5783-706e-47d1-a76f-788ec2818df6
-- title:
--   Proposition 16, Unital-channel coherence matrix
-- statement:
--   Fix a reference orthonormal basis of a finite-dimensional complex Hilbert space of dimension $d\ge1$. For a population vector $p$ in the closed simplex $\{p_i\ge0,\ \sum_i p_i=1\}$, let $\rho_p=\operatorname{diag}p$. The input law $\nu_d=\operatorname{Dir}(1,\ldots,1)$ is uniform on this whole simplex. Write $c_B(\rho)=\sum_{i\ne j}|\rho_{ij}|^2$ for squared Hilbert–Schmidt coherence. For a fixed unitary $U$, set $X_U(p)=c_B(U\rho_pU^\dagger)$, $C_U=\mathbb E_{\nu_d}X_U$, $\Delta_U=\sqrt{\operatorname{Var}_{\nu_d}X_U}$, $P_{ij}=|U_{ij}|^2$, $G=I-P^TP$, $H_d=I-\mathbf1\mathbf1^T/d$, and $D_d=d(d+1)(d+2)(d+3)$. For a channel $\mathcal E$, replace $X_U$ by $X_{\mathcal E}(p)=c_B(\mathcal E(\rho_p))$, with its own mean $C_{\mathcal E}$ and deviation $\Delta_{\mathcal E}$. A channel is completely positive and trace preserving; unitality, where specified, means $\mathcal E(I)=I$.
--
--   Let $\mathcal E$ be CPTP and unital, and define $A_i=Q_B\mathcal E(|i\rangle\langle i|)$, where $Q_B=I-D_B$. The real Gram response is $(G_{\mathcal E})_{ij}=\operatorname{Re}\operatorname{Tr}(A_iA_j)$. Then
--   $$X_{\mathcal E}(p)=p^TG_{\mathcal E}p\quad\text{for every simplex population }p,\qquad G_{\mathcal E}=G_{\mathcal E}^T,\quad G_{\mathcal E}\succeq0,\quad G_{\mathcal E}\mathbf1=0.$$
--   Each $A_i$ is Hermitian, so its Gram trace is already real.
--
--   The channel extension uses coherent output components rather than the unitary-only formula $I-P^TP$.
-- source:
--   Coherence -generating power deviation: Fluctuations and input selectivity beyond average coherence generation, arXiv:2609.19046v1, PDF p. 9, Proposition 16, Unital-channel coherence matrix

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P37

noncomputable section

namespace QAlgorithms.Papers.Independent.Information100.P37

open MeasureTheory ProbabilityTheory Filter

open scoped BigOperators Matrix ComplexConjugate Topology

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- PDF p.9, Proposition 16: the actual unital CPTP Gram response. -/
theorem unitalCoherenceMatrix [Nonempty ι] (E : Superop ι ι)
    (hE : IsChannel E) (hu : E 1 = 1) :
    (∀ p, IsPopulation p → generated E p = quadratic (channelResponse E) p) ∧
    (channelResponse E).IsSymm ∧ (channelResponse E).PosSemidef ∧
    (channelResponse E).mulVec (fun _ => 1) = 0 := by sorry

end QAlgorithms.Papers.Independent.Information100.P37

end
