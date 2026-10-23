-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P37_krausEntryGram
-- name    : QAlgorithms.Papers.Independent.Information100.P37.krausEntryGram
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T11:19:00.6506+00:00
-- url     : https://prove2.me/theorems/030272dd-ee4d-46ea-b5d3-085d9d995a62
-- title:
--   §VII.C, Eq. (80): Kraus-entry Gram formula
-- statement:
--   Fix a reference orthonormal basis of a finite-dimensional complex Hilbert space of dimension $d\ge1$. For a population vector $p$ in the closed simplex $\{p_i\ge0,\ \sum_i p_i=1\}$, let $\rho_p=\operatorname{diag}p$. The input law $\nu_d=\operatorname{Dir}(1,\ldots,1)$ is uniform on this whole simplex. Write $c_B(\rho)=\sum_{i\ne j}|\rho_{ij}|^2$ for squared Hilbert–Schmidt coherence. For a fixed unitary $U$, set $X_U(p)=c_B(U\rho_pU^\dagger)$, $C_U=\mathbb E_{\nu_d}X_U$, $\Delta_U=\sqrt{\operatorname{Var}_{\nu_d}X_U}$, $P_{ij}=|U_{ij}|^2$, $G=I-P^TP$, $H_d=I-\mathbf1\mathbf1^T/d$, and $D_d=d(d+1)(d+2)(d+3)$. For a channel $\mathcal E$, replace $X_U$ by $X_{\mathcal E}(p)=c_B(\mathcal E(\rho_p))$, with its own mean $C_{\mathcal E}$ and deviation $\Delta_{\mathcal E}$. A channel is completely positive and trace preserving; unitality, where specified, means $\mathcal E(I)=I$.
--
--   Let $\mathcal E$ be CPTP and unital, with a finite normalized Kraus family $E_k$ satisfying $\mathcal E(M)=\sum_kE_kME_k^\dagger$ for every matrix and $\sum_kE_k^\dagger E_k=I$. For $A_i=Q_B\mathcal E(|i\rangle\langle i|)$ and $(G_{\mathcal E})_{ij}=\operatorname{Re}\operatorname{Tr}(A_iA_j)$,
--   $$(G_{\mathcal E})_{ij}=\operatorname{Re}\sum_{l\ne m}\overline{\left(\sum_k(E_k)_{li}\overline{(E_k)_{mi}}\right)}\left(\sum_r(E_r)_{lj}\overline{(E_r)_{mj}}\right).$$
--   The first entire bracket is conjugated.
--
--   This expresses the channel Gram matrix directly in Kraus entries.
-- source:
--   Coherence -generating power deviation: Fluctuations and input selectivity beyond average coherence generation, arXiv:2609.19046v1, PDF p. 9, §VII.C, Eq. (80): Kraus-entry Gram formula

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P37

noncomputable section

namespace QAlgorithms.Papers.Independent.Information100.P37

open MeasureTheory ProbabilityTheory Filter

open scoped BigOperators Matrix ComplexConjugate Topology

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- PDF p.9, (80): Kraus entry Gram formula, retaining the outer first-factor conjugate. -/
theorem krausEntryGram [Nonempty ι] {K : Type*} [Fintype K]
    (E : Superop ι ι) (hE : IsChannel E) (hu : E 1 = 1)
    (A : K → Matrix ι ι ℂ) (hA : IsKrausFamily A) (hrep : ∀ M, E M = krausApply A M) :
    ∀ i j, channelResponse E i j =
      (∑ l : ι, ∑ m : ι, if l = m then (0 : ℂ) else
        conj (∑ k, A k l i * conj (A k m i)) * (∑ r, A r l j * conj (A r m j))).re := by sorry

end QAlgorithms.Papers.Independent.Information100.P37

end
