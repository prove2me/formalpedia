-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P29_blockAverageBound
-- name    : QAlgorithms.Papers.Independent.Advance50.P29.blockAverageBound
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T22:20:50.572252+00:00
-- url     : https://prove2.me/theorems/7210ede6-343a-4ef4-bcd6-be0d82539efc
-- title:
--   §7.4: explicit average fidelity of floor-exponential block codes
-- statement:
--   Let $Q$ and $Q^{\prime}$ be finite complex Hilbert spaces of positive dimensions $M$ and $D$. A density operator is positive semidefinite with trace one. All logarithms and entropies are in bits. Write $\pi=I_Q/M$. For a nonzero code subspace $C\subset Q$ of dimension $K$, let $\pi_C=\Pi_C/K$. Write $F_e(C,\mathcal N)=\max_{\mathcal R}F_e(\pi_C,\mathcal R\circ\mathcal N)$, where $\mathcal R:B(Q^{\prime})\to B(Q)$ ranges over all CPTP recovery maps and state entanglement fidelity is squared and unconditional. Fix any $K$-dimensional seed code $C_0$ and average $C=UC_0$ over normalized Haar measure on the entire unitary group of $Q$; denote this expectation by $[\,\cdot\,]_K$. All displayed Haar integrands are integrable. For a state $\rho$, put $I(\rho,\mathcal N)=S(\mathcal N(\rho))-S_e(\rho,\mathcal N)$, where $S$ is von Neumann entropy and $S_e$ is the entropy of the reference/output state after applying $\mathcal N$ to a purification of $\rho$. Fix a minimal Kraus representation $(A_i)_{i\in L}$ of a CPTP channel $\mathcal N$, with $\operatorname{tr}(A_i^\dagger A_j)=0$ for $i\ne j$. Set $P_i=M^{-1}\operatorname{tr}(A_i^\dagger A_i)$ and fix $\varepsilon>0$. For a word $w=(i_1,\ldots,i_n)$ put $A_w=A_{i_1}\otimes\cdots\otimes A_{i_n}$ and $p_w=\prod_tP_{i_t}$. Keep exactly those words with $2^{-n(H(P)+\varepsilon)}\le p_w\le2^{-n(H(P)-\varepsilon)}$, defining $\mathcal N_{\varepsilon,n}(X)=\sum_{w\ {\rm typical}}A_wXA_w^\dagger$. Let $\Pi_{\varepsilon,n}$ be the spectral projection of $\mathcal N(\pi)^{\otimes n}$ onto the closed eigenvalue window $[2^{-n(S(\mathcal N(\pi))+\varepsilon)},2^{-n(S(\mathcal N(\pi))-\varepsilon)}]$ and define $\widetilde{\mathcal N}_{\varepsilon,n}(X)=\Pi_{\varepsilon,n}\mathcal N_{\varepsilon,n}(X)\Pi_{\varepsilon,n}$. Also set $\pi_n=I_{Q^{\otimes n}}/M^n$. There is $\psi_3>0$, depending only on the fixed channel, representation, and $\varepsilon$, with the following property. For $R\ge0$ and positive integer $n$, suppose $K_n=\lfloor2^{nR}\rfloor\le M^n$, and average over any seed of dimension $K_n$ in $Q^{\otimes n}$. Write $|\mathcal T|$ for minimum Kraus length. Then
--
--   $$
--   [F_e(C,\mathcal N^{\otimes n})]_{K_n}\ge\operatorname{tr}\widetilde{\mathcal N}_{\varepsilon,n}(\pi_n)-\sqrt{K_n|\widetilde{\mathcal N}_{\varepsilon,n}|}\,\|\widetilde{\mathcal N}_{\varepsilon,n}(\pi_n)\|_F\ge1-4e^{-n\psi_3}-2^{\frac n2(R-I(\pi,\mathcal N)+4\varepsilon)}.
--   $$
--
--   This is the explicit block-average estimate driving the coherent-information achievability argument.
-- source:
--   A random-coding based proof for the quantum coding theorem, arXiv:0712.2558v1, PDF p. 18, §7.4: explicit average fidelity of floor-exponential block codes

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

/-- PDF p.18, §7.4: explicit Haar-average bound for floor-exponential code dimensions.
The exponent is n/2 times (R - I + 4 epsilon); the decay constant is independent of R,n,C. -/
theorem blockAverageBound [Nonempty I] [Nonempty J] [Nonempty L]
    (A : L → Matrix J I ℂ) (hA : IsKrausFamily A) (hm : MinimalKraus A)
    (ho : ∀ i j, i ≠ j → ((A i)ᴴ * A j).trace = 0)
    (epsilon : ℝ) (he : 0 < epsilon) :
    ∃ psi : ℝ, 0 < psi ∧ ∀ (R : ℝ), 0 ≤ R → ∀ n : ℕ, 0 < n →
      ∀ C : CodeProjection (Fin n → I), C.dimension = ⌊(2 : ℝ) ^ ((n : ℝ) * R)⌋₊ →
      Integrable (fun U => recoveredEntanglementFidelity (piSuperop (fun _ : Fin n => krausApply A))
        (rotatedDensity C U)) (Schur.unitaryHaar (Fintype.card (Fin n → I))) ∧
      ((reducedOperation A epsilon n (mixed (Fin n → I))).trace.re -
        Real.sqrt ((C.dimension : ℝ) * operationLength (reducedOperation A epsilon n)) *
          Real.sqrt (frobeniusSq (reducedOperation A epsilon n (mixed (Fin n → I)))) ≤
        codeAverage C (recoveredEntanglementFidelity (piSuperop (fun _ : Fin n => krausApply A)))) ∧
      1 - 4 * Real.exp (-(n : ℝ) * psi) -
        (2 : ℝ) ^ ((n : ℝ) / 2 *
          (R - coherentInformation (krausApply A) (mixed I) + 4 * epsilon)) ≤
        (reducedOperation A epsilon n (mixed (Fin n → I))).trace.re -
          Real.sqrt ((C.dimension : ℝ) * operationLength (reducedOperation A epsilon n)) *
            Real.sqrt (frobeniusSq (reducedOperation A epsilon n (mixed (Fin n → I)))) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P29

end
