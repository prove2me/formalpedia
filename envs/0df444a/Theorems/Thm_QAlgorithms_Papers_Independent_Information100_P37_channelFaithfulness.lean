-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P37_channelFaithfulness
-- name    : QAlgorithms.Papers.Independent.Information100.P37.channelFaithfulness
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T11:18:01.315901+00:00
-- url     : https://prove2.me/theorems/f2494448-6ea0-4e5a-ab80-15861afb1aa9
-- title:
--   §VII.B, Eq. (77): channel faithfulness
-- statement:
--   Fix a reference orthonormal basis of a finite-dimensional complex Hilbert space of dimension $d\ge1$. For a population vector $p$ in the closed simplex $\{p_i\ge0,\ \sum_i p_i=1\}$, let $\rho_p=\operatorname{diag}p$. The input law $\nu_d=\operatorname{Dir}(1,\ldots,1)$ is uniform on this whole simplex. Write $c_B(\rho)=\sum_{i\ne j}|\rho_{ij}|^2$ for squared Hilbert–Schmidt coherence. For a fixed unitary $U$, set $X_U(p)=c_B(U\rho_pU^\dagger)$, $C_U=\mathbb E_{\nu_d}X_U$, $\Delta_U=\sqrt{\operatorname{Var}_{\nu_d}X_U}$, $P_{ij}=|U_{ij}|^2$, $G=I-P^TP$, $H_d=I-\mathbf1\mathbf1^T/d$, and $D_d=d(d+1)(d+2)(d+3)$. For a channel $\mathcal E$, replace $X_U$ by $X_{\mathcal E}(p)=c_B(\mathcal E(\rho_p))$, with its own mean $C_{\mathcal E}$ and deviation $\Delta_{\mathcal E}$. A channel is completely positive and trace preserving; unitality, where specified, means $\mathcal E(I)=I$.
--
--   For a CPTP unital channel $\mathcal E$, with $D_B$ the diagonal projection and $Q_B=I-D_B$,
--   $$(C_{\mathcal E}=0\ \text{and}\ \Delta_{\mathcal E}=0)\quad\Longleftrightarrow\quad Q_B\mathcal E D_B=0.$$
--   The right-hand side is an equality of superoperators on every matrix, and expresses absence of coherence generation from diagonal inputs.
--
--   This preserves the simultaneous-zero criterion and does not replace it by the stronger commutation with dephasing.
-- source:
--   Coherence -generating power deviation: Fluctuations and input selectivity beyond average coherence generation, arXiv:2609.19046v1, PDF p. 9, §VII.B, Eq. (77): channel faithfulness

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P37

noncomputable section

namespace QAlgorithms.Papers.Independent.Information100.P37

open MeasureTheory ProbabilityTheory Filter

open scoped BigOperators Matrix ComplexConjugate Topology

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- PDF p.9, (77): simultaneous zeros characterize Q E D=0, not commutation. -/
theorem channelFaithfulness [Nonempty ι] (E : Superop ι ι)
    (hE : IsChannel E) (hu : E 1 = 1) :
    (cgp E = 0 ∧ cgpd E = 0) ↔ ∀ M : Matrix ι ι ℂ, offDiagonal (E (Matrix.diagonal (Matrix.diag M))) = 0 := by sorry

end QAlgorithms.Papers.Independent.Information100.P37

end
