-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P29_reducedOperationBounds
-- name    : QAlgorithms.Papers.Independent.Advance50.P29.reducedOperationBounds
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T22:18:54.193044+00:00
-- url     : https://prove2.me/theorems/71d165c3-fe40-4e30-ad72-81fa1952d103
-- title:
--   §7.3, (27)–(29); Appendix D, (34)–(36): projected typical operation bounds
-- statement:
--   Let $Q$ and $Q^{\prime}$ be finite complex Hilbert spaces of positive dimensions $M$ and $D$. A density operator is positive semidefinite with trace one. All logarithms and entropies are in bits. Write $\pi=I_Q/M$. For a state $\rho$, put $I(\rho,\mathcal N)=S(\mathcal N(\rho))-S_e(\rho,\mathcal N)$, where $S$ is von Neumann entropy and $S_e$ is the entropy of the reference/output state after applying $\mathcal N$ to a purification of $\rho$. Fix a minimal Kraus representation $(A_i)_{i\in L}$ of a CPTP channel $\mathcal N$, with $\operatorname{tr}(A_i^\dagger A_j)=0$ for $i\ne j$. Set $P_i=M^{-1}\operatorname{tr}(A_i^\dagger A_i)$ and fix $\varepsilon>0$. For a word $w=(i_1,\ldots,i_n)$ put $A_w=A_{i_1}\otimes\cdots\otimes A_{i_n}$ and $p_w=\prod_tP_{i_t}$. Keep exactly those words with $2^{-n(H(P)+\varepsilon)}\le p_w\le2^{-n(H(P)-\varepsilon)}$, defining $\mathcal N_{\varepsilon,n}(X)=\sum_{w\ {\rm typical}}A_wXA_w^\dagger$. Let $\Pi_{\varepsilon,n}$ be the spectral projection of $\mathcal N(\pi)^{\otimes n}$ onto the closed eigenvalue window $[2^{-n(S(\mathcal N(\pi))+\varepsilon)},2^{-n(S(\mathcal N(\pi))-\varepsilon)}]$ and define $\widetilde{\mathcal N}_{\varepsilon,n}(X)=\Pi_{\varepsilon,n}\mathcal N_{\varepsilon,n}(X)\Pi_{\varepsilon,n}$. Also set $\pi_n=I_{Q^{\otimes n}}/M^n$. Write $|\mathcal T|$ for minimum Kraus length and $\|X\|_F^2=\operatorname{tr}X^\dagger X$. There exists $\psi_3>0$, independent of positive integer $n$, such that
--
--   $$
--   |\widetilde{\mathcal N}_{\varepsilon,n}|\le2^{n(S_e(\pi,\mathcal N)+\varepsilon)},\qquad\operatorname{tr}\widetilde{\mathcal N}_{\varepsilon,n}(\pi_n)\ge1-4e^{-n\psi_3},\qquad\|\widetilde{\mathcal N}_{\varepsilon,n}(\pi_n)\|_F^2\le2^{-n(S(\mathcal N(\pi))-3\varepsilon)}.
--   $$
--
--   These three bounds establish approximate uniformity and unitality of the constructed operation.
-- source:
--   A random-coding based proof for the quantum coding theorem, arXiv:0712.2558v1, PDF p. 17, §7.3, (27)–(29); Appendix D, (34)–(36): projected typical operation bounds

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P29

noncomputable section

namespace QAlgorithms.Papers.Independent.Advance50.P29

open QAlgorithms MeasureTheory Filter

open QAlgorithms.Papers.Independent.Information100.P22
  (densityPurification coherentInformation singleUseInformation mixed)

open QAlgorithms.Papers.Independent.Information100.P27 (shannon)

open QAlgorithms.Papers.Independent.Dependency50.P48 (wordProbability)

open QAlgorithms.Papers.Independent.Bridge50.P43 (tensorDensity)

open scoped Matrix ComplexConjugate ComplexOrder Topology

attribute [local instance] Classical.propDecidable

variable {I J E L : Type} [Fintype I] [DecidableEq I]

variable [Fintype J] [DecidableEq J] [Fintype E] [DecidableEq E]

variable [Fintype L] [DecidableEq L]

/-- PDF pp.17,22–23, (27)–(29)=(34)–(36): output-projected typical operation bounds.
The Frobenius norm is squared and the entropy correction is exactly 3 epsilon. -/
theorem reducedOperationBounds [Nonempty I] [Nonempty J] [Nonempty L]
    (A : L → Matrix J I ℂ) (hA : IsKrausFamily A) (hm : MinimalKraus A)
    (ho : ∀ i j, i ≠ j → ((A i)ᴴ * A j).trace = 0)
    (epsilon : ℝ) (he : 0 < epsilon) :
    ∃ psi : ℝ, 0 < psi ∧ ∀ n : ℕ, 0 < n →
      (operationLength (reducedOperation A epsilon n) : ℝ) ≤
        (2 : ℝ) ^ ((n : ℝ) * (exchangeEntropy (krausApply A) (mixed I) + epsilon)) ∧
      1 - 4 * Real.exp (-(n : ℝ) * psi) ≤
        (reducedOperation A epsilon n (mixed (Fin n → I))).trace.re ∧
      frobeniusSq (reducedOperation A epsilon n (mixed (Fin n → I))) ≤
        (2 : ℝ) ^ (-(n : ℝ) * (vnEntropy (krausApply A (mixed I)) - 3 * epsilon)) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P29

end
