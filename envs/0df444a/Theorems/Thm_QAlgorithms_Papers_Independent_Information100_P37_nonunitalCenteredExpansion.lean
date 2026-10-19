-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P37_nonunitalCenteredExpansion
-- name    : QAlgorithms.Papers.Independent.Information100.P37.nonunitalCenteredExpansion
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T11:18:29.952991+00:00
-- url     : https://prove2.me/theorems/7b783e8f-1439-4f7e-bc6d-3c2e5f6ccaa7
-- title:
--   §VII.B, Eqs. (78)–(79): affine centered expansion
-- statement:
--   Fix a reference orthonormal basis of a finite-dimensional complex Hilbert space of dimension $d\ge1$. For a population vector $p$ in the closed simplex $\{p_i\ge0,\ \sum_i p_i=1\}$, let $\rho_p=\operatorname{diag}p$. The input law $\nu_d=\operatorname{Dir}(1,\ldots,1)$ is uniform on this whole simplex. Write $c_B(\rho)=\sum_{i\ne j}|\rho_{ij}|^2$ for squared Hilbert–Schmidt coherence. For a fixed unitary $U$, set $X_U(p)=c_B(U\rho_pU^\dagger)$, $C_U=\mathbb E_{\nu_d}X_U$, $\Delta_U=\sqrt{\operatorname{Var}_{\nu_d}X_U}$, $P_{ij}=|U_{ij}|^2$, $G=I-P^TP$, $H_d=I-\mathbf1\mathbf1^T/d$, and $D_d=d(d+1)(d+2)(d+3)$. For a channel $\mathcal E$, replace $X_U$ by $X_{\mathcal E}(p)=c_B(\mathcal E(\rho_p))$, with its own mean $C_{\mathcal E}$ and deviation $\Delta_{\mathcal E}$. A channel is completely positive and trace preserving; unitality, where specified, means $\mathcal E(I)=I$.
--
--   Let $\mathcal E$ be any CPTP channel, without a unitality assumption. Define $A_i=Q_B\mathcal E(|i\rangle\langle i|)$ and $a_0=d^{-1}\sum_iA_i=Q_B\mathcal E(I/d)$. For $x=p-\mathbf1/d$ and any simplex population $p$,
--   $$Q_B\mathcal E(\rho_p)=a_0+\sum_ix_iA_i,$$
--   $$X_{\mathcal E}(p)=\|a_0\|_{\rm HS}^2+2\sum_ix_i\operatorname{Re}\operatorname{Tr}(a_0^\dagger A_i)+\sum_{i,j}x_ix_j\operatorname{Re}\operatorname{Tr}(A_i^\dagger A_j).$$
--   The offset and linear contribution are allowed to vanish for particular channels.
--
--   The affine expansion records the change of regime when unitality is dropped.
-- source:
--   Coherence -generating power deviation: Fluctuations and input selectivity beyond average coherence generation, arXiv:2609.19046v1, PDF p. 9, §VII.B, Eqs. (78)–(79): affine centered expansion

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P37

noncomputable section

namespace QAlgorithms.Papers.Independent.Information100.P37

open MeasureTheory ProbabilityTheory Filter

open scoped BigOperators Matrix ComplexConjugate Topology

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- PDF p.9, (78)--(79): general CPTP affine expansion, with unitality dropped. -/
theorem nonunitalCenteredExpansion [Nonempty ι] (E : Superop ι ι) (hE : IsChannel E) :
    channelOffset E = offDiagonal (E ((1 / (Fintype.card ι : ℂ)) • (1 : Matrix ι ι ℂ))) ∧
    (∀ p, IsPopulation p →
      offDiagonal (E (inputDensity p)) = channelOffset E + ∑ i, (centered p i : ℂ) • channelOutput E i ∧
      generated E p = frobNorm (channelOffset E) ^ 2 +
        2 * (∑ i, centered p i * (((channelOffset E)ᴴ * channelOutput E i).trace).re) +
        ∑ i, ∑ j, centered p i * centered p j * (((channelOutput E i)ᴴ * channelOutput E j).trace).re) := by sorry

end QAlgorithms.Papers.Independent.Information100.P37

end
