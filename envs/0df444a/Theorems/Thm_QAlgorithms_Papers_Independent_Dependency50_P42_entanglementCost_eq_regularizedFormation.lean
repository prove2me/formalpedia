-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P42_entanglementCost_eq_regularizedFormation
-- name    : QAlgorithms.Papers.Independent.Dependency50.P42.entanglementCost_eq_regularizedFormation
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T16:53:50.140342+00:00
-- url     : https://prove2.me/theorems/2949c6e9-a0b8-401c-a6f5-aeb891ce712e
-- title:
--   Entanglement cost equals regularized entanglement of formation
-- statement:
--   Let $\rho$ be a positive semidefinite, trace-one operator on $\mathbb C^a\otimes\mathbb C^b$, with positive integers $a,b$. Every tensor power retains the bipartition $A^{\otimes n}:B^{\otimes n}$.
--
--   Write $E_f(\tau)$ for the minimum, over all finite ensembles $\tau=\sum_i p_i|\psi_i\rangle\langle\psi_i|$ with $p_i\ge0$, $\sum_i p_i=1$ and unit vectors $\psi_i$, of $\sum_i p_i S(\operatorname{Tr}_B|\psi_i\rangle\langle\psi_i|)$. Here $S$ is von Neumann entropy with base-two logarithms and $0\log 0=0$, so entanglement is measured in ebits.
--
--   For density operators define the root fidelity $F(\tau,\omega)=\operatorname{Tr}\sqrt{\sqrt\tau\,\omega\sqrt\tau}$ and the paper-normalized Bures distance $D(\tau,\omega)=2\sqrt{1-F(\tau,\omega)}$.
--
--   The cost $E_c(\tau)$ is the infimum of real rates $E$ such that, for every $\epsilon,\delta>0$, there exist integers $m\ge0$, $n\ge1$ and a deterministic LOCC map $L$ for which $|E-m/n|\le\delta$ and $D(L(\Psi_-^{\otimes m}),\tau^{\otimes n})\le\epsilon$. Here $\Psi_-$ is the density matrix of $(|01\rangle-|10\rangle)/\sqrt2$. LOCC means finite adaptive local quantum operations with unrestricted two-way classical communication; outputs are averaged over all outcomes, and local ancillary systems may be introduced and discarded.
--
--   The positive-copy quotients converge to the operational cost, and their regularized value equals that cost:
--
--   $$\lim_{n\to\infty}\frac{E_f(\rho^{\otimes n})}{n}=E_c(\rho)=E_f^\infty(\rho).$$
--
--   This identifies the deterministic asymptotic singlet cost with the regularized convex-roof quantity.
--
--   **Formalization Note** The sequence is indexed by $n+1$ to avoid a zero denominator. The named regularization is the infimum of positive-copy quotients, and convergence is explicitly included.
-- source:
--   The asymptotic entanglement cost of preparing a quantum state, arXiv:quant-ph/0008134v1, PDF p. 2, Theorem 1 / Eq.(7), continued on PDF p.3

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P42

namespace QAlgorithms.Papers.Independent.Dependency50.P42

open scoped Matrix ComplexConjugate ComplexOrder

open Information100.P21 (Op)

noncomputable section

/-- PDF pp.2--3, Theorem 1 / Eq.(7): cost equals regularized formation, and the
positive-copy quotients actually converge to that cost. -/
theorem entanglementCost_eq_regularizedFormation {a b : ℕ}
    (ha : 0 < a) (hb : 0 < b) (rho : Op (Fin a × Fin b)) (hrho : IsDensityMatrix rho) :
    entanglementCost paperBures rho = regularizedFormation rho ∧
      Filter.Tendsto (formationSequence rho) Filter.atTop
        (nhds (entanglementCost paperBures rho)) := by sorry

end

end QAlgorithms.Papers.Independent.Dependency50.P42
