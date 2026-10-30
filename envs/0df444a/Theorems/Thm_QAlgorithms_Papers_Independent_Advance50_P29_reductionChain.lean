-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P29_reductionChain
-- name    : QAlgorithms.Papers.Independent.Advance50.P29.reductionChain
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T22:19:51.726157+00:00
-- url     : https://prove2.me/theorems/34fa2353-176a-472f-a712-122af2d44eb3
-- title:
--   §7.4, (30): monotonicity along the constructed reductions
-- statement:
--   Let $Q$ and $Q^{\prime}$ be finite complex Hilbert spaces of positive dimensions $M$ and $D$. A density operator is positive semidefinite with trace one. All logarithms and entropies are in bits. Write $\pi=I_Q/M$. For a nonzero code subspace $C\subset Q$ of dimension $K$, let $\pi_C=\Pi_C/K$. Write $F_e(C,\mathcal N)=\max_{\mathcal R}F_e(\pi_C,\mathcal R\circ\mathcal N)$, where $\mathcal R:B(Q^{\prime})\to B(Q)$ ranges over all CPTP recovery maps and state entanglement fidelity is squared and unconditional. Fix a minimal Kraus representation $(A_i)_{i\in L}$ of a CPTP channel $\mathcal N$, with $\operatorname{tr}(A_i^\dagger A_j)=0$ for $i\ne j$. Set $P_i=M^{-1}\operatorname{tr}(A_i^\dagger A_i)$ and fix $\varepsilon>0$. For a word $w=(i_1,\ldots,i_n)$ put $A_w=A_{i_1}\otimes\cdots\otimes A_{i_n}$ and $p_w=\prod_tP_{i_t}$. Keep exactly those words with $2^{-n(H(P)+\varepsilon)}\le p_w\le2^{-n(H(P)-\varepsilon)}$, defining $\mathcal N_{\varepsilon,n}(X)=\sum_{w\ {\rm typical}}A_wXA_w^\dagger$. Let $\Pi_{\varepsilon,n}$ be the spectral projection of $\mathcal N(\pi)^{\otimes n}$ onto the closed eigenvalue window $[2^{-n(S(\mathcal N(\pi))+\varepsilon)},2^{-n(S(\mathcal N(\pi))-\varepsilon)}]$ and define $\widetilde{\mathcal N}_{\varepsilon,n}(X)=\Pi_{\varepsilon,n}\mathcal N_{\varepsilon,n}(X)\Pi_{\varepsilon,n}$. Also set $\pi_n=I_{Q^{\otimes n}}/M^n$. For every positive integer $n$ and every nonzero code $C\subset Q^{\otimes n}$,
--
--   $$
--   F_e(C,\mathcal N^{\otimes n})\ge F_e(C,\mathcal N_{\varepsilon,n})\ge F_e(C,\widetilde{\mathcal N}_{\varepsilon,n}).
--   $$
--
--   This transfers the fidelity estimate for the constructed truncations back to the original channel.
-- source:
--   A random-coding based proof for the quantum coding theorem, arXiv:0712.2558v1, PDF p. 17, §7.4, (30): monotonicity along the constructed reductions

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

/-- PDF p.17, (30): monotonicity along the two actual constructed reductions.
Recovery remains CPTP: a trace-decreasing composed recovery can be completed. -/
theorem reductionChain [Nonempty I] [Nonempty J] [Nonempty L]
    (A : L → Matrix J I ℂ) (hA : IsKrausFamily A) (hm : MinimalKraus A)
    (ho : ∀ i j, i ≠ j → ((A i)ᴴ * A j).trace = 0)
    (epsilon : ℝ) (he : 0 < epsilon) (n : ℕ) (hn : 0 < n)
    (C : CodeProjection (Fin n → I)) :
    recoveredEntanglementFidelity (reducedOperation A epsilon n) (codeDensity C) ≤
      recoveredEntanglementFidelity (typicalOperation A epsilon n) (codeDensity C) ∧
    recoveredEntanglementFidelity (typicalOperation A epsilon n) (codeDensity C) ≤
      recoveredEntanglementFidelity (piSuperop (fun _ : Fin n => krausApply A)) (codeDensity C) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P29

end
