-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P42_regularizedFormation_lowerBound
-- name    : QAlgorithms.Papers.Independent.Dependency50.P42.regularizedFormation_lowerBound
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T16:57:42.563276+00:00
-- url     : https://prove2.me/theorems/f10d6f0f-f5f5-4efd-ae49-d7d5f0f91d24
-- title:
--   Regularized formation lower-bounds cost
-- statement:
--   Let $\rho$ be a positive semidefinite, trace-one operator on $\mathbb C^a\otimes\mathbb C^b$, with positive integers $a,b$. Every tensor power retains the bipartition $A^{\otimes n}:B^{\otimes n}$.
--
--   Write $E_f(\tau)$ for the minimum, over all finite ensembles $\tau=\sum_i p_i|\psi_i\rangle\langle\psi_i|$ with $p_i\ge0$, $\sum_i p_i=1$ and unit vectors $\psi_i$, of $\sum_i p_i S(\operatorname{Tr}_B|\psi_i\rangle\langle\psi_i|)$. Here $S$ is von Neumann entropy with base-two logarithms and $0\log 0=0$, so entanglement is measured in ebits.
--
--   For density operators define the root fidelity $F(\tau,\omega)=\operatorname{Tr}\sqrt{\sqrt\tau\,\omega\sqrt\tau}$ and the paper-normalized Bures distance $D(\tau,\omega)=2\sqrt{1-F(\tau,\omega)}$.
--
--   The cost $E_c(\tau)$ is the infimum of real rates $E$ such that, for every $\epsilon,\delta>0$, there exist integers $m\ge0$, $n\ge1$ and a deterministic LOCC map $L$ for which $|E-m/n|\le\delta$ and $D(L(\Psi_-^{\otimes m}),\tau^{\otimes n})\le\epsilon$. Here $\Psi_-$ is the density matrix of $(|01\rangle-|10\rangle)/\sqrt2$. LOCC means finite adaptive local quantum operations with unrestricted two-way classical communication; outputs are averaged over all outcomes, and local ancillary systems may be introduced and discarded.
--
--   Write $E_f^\infty(\rho)$ for the limit of $E_f(\rho^{\otimes n})/n$ over positive integers $n$, whose existence is asserted separately.
--
--   One has
--
--   $$E_f^\infty(\rho)\le E_c(\rho).$$
--
--   This is the converse to the regularized preparation upper bound.
-- source:
--   The asymptotic entanglement cost of preparing a quantum state, arXiv:quant-ph/0008134v1, PDF p. 4, Lemma 3

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P42

namespace QAlgorithms.Papers.Independent.Dependency50.P42

open scoped Matrix ComplexConjugate ComplexOrder

open Information100.P21 (Op)

noncomputable section

/-- PDF p.4, Lemma 3: the converse inequality. Monotonicity, continuity and an
optimal protocol sequence are not made hypotheses on rho. -/
theorem regularizedFormation_lowerBound {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (rho : Op (Fin a × Fin b)) (hrho : IsDensityMatrix rho) :
    regularizedFormation rho ≤ entanglementCost paperBures rho := by sorry

end

end QAlgorithms.Papers.Independent.Dependency50.P42
