-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P42_dimensionUniformMetric_costs_agree
-- name    : QAlgorithms.Papers.Independent.Dependency50.P42.dimensionUniformMetric_costs_agree
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T17:01:54.90721+00:00
-- url     : https://prove2.me/theorems/1bfea0e7-9cc1-4b70-9b83-d5eb111a09a3
-- title:
--   Dimension-uniform equivalent metrics preserve both costs
-- statement:
--   Let $\rho$ be a positive semidefinite, trace-one operator on $\mathbb C^a\otimes\mathbb C^b$, with positive integers $a,b$. Every tensor power retains the bipartition $A^{\otimes n}:B^{\otimes n}$.
--
--   Write $E_f(\tau)$ for the minimum, over all finite ensembles $\tau=\sum_i p_i|\psi_i\rangle\langle\psi_i|$ with $p_i\ge0$, $\sum_i p_i=1$ and unit vectors $\psi_i$, of $\sum_i p_i S(\operatorname{Tr}_B|\psi_i\rangle\langle\psi_i|)$. Here $S$ is von Neumann entropy with base-two logarithms and $0\log 0=0$, so entanglement is measured in ebits.
--
--   For density operators define the root fidelity $F(\tau,\omega)=\operatorname{Tr}\sqrt{\sqrt\tau\,\omega\sqrt\tau}$ and the paper-normalized Bures distance $D(\tau,\omega)=2\sqrt{1-F(\tau,\omega)}$.
--
--   The cost $E_c(\tau)$ is the infimum of real rates $E$ such that, for every $\epsilon,\delta>0$, there exist integers $m\ge0$, $n\ge1$ and a deterministic LOCC map $L$ for which $|E-m/n|\le\delta$ and $D(L(\Psi_-^{\otimes m}),\tau^{\otimes n})\le\epsilon$. Here $\Psi_-$ is the density matrix of $(|01\rangle-|10\rangle)/\sqrt2$. LOCC means finite adaptive local quantum operations with unrestricted two-way classical communication; outputs are averaged over all outcomes, and local ancillary systems may be introduced and discarded.
--
--   The alternative cost $E_{\mathrm{alt}}(\tau)$ is the infimum over rates obeying the same requirements except that, for each $\epsilon,\delta>0$, there must exist $N$ such that every integer $n>N$ has a suitable $m$ and LOCC map $L$. Both $m$ and $L$ may depend on $n$.
--
--   Write $E_f^\infty(\rho)$ for the limit of $E_f(\rho^{\otimes n})/n$ over positive integers $n$, whose existence is asserted separately.
--
--   Let $M_{a,b}$ be a metric on the density operators on $\mathbb C^a\otimes\mathbb C^b$ for every $a,b\ge1$. Assume dimension-uniform equivalence at zero: for every $\epsilon>0$ there is $\eta>0$, chosen independently of $a,b$ and the states, such that $M_{a,b}(\tau,\omega)\le\eta$ implies $D(\tau,\omega)\le\epsilon$. Assume also the reverse implication with $M$ and $D$ interchanged, with its own uniform tolerance. Define $E_c^M$ and $E_{\mathrm{alt}}^M$ by replacing $D$ by $M$ in their respective operational definitions. Then
--
--   $$E_c^M(\rho)=E_c(\rho)=E_f^\infty(\rho),\qquad E_{\mathrm{alt}}^M(\rho)=E_{\mathrm{alt}}(\rho)=E_f^\infty(\rho).$$
--
--   This makes the conditional metric-independence extension precise in the regime of growing tensor-power dimensions.
--
--   **Formalization Note** The source says “they should hold.” The statement interprets the specified dimension-independent equivalence as uniform control near zero in both directions; no rate for the controlling moduli is prescribed.
-- source:
--   The asymptotic entanglement cost of preparing a quantum state, arXiv:quant-ph/0008134v1, PDF p. 5, Section III, final sentence

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P42

namespace QAlgorithms.Papers.Independent.Dependency50.P42

open scoped Matrix ComplexConjugate ComplexOrder

open Information100.P21 (Op)

noncomputable section

/-- PDF p.5, final paragraph: conditional metric independence for both costs.
The tentative dimension-independent equivalence is interpreted as uniform
two-sided control at zero, explicitly before the growing dimensions. -/
theorem dimensionUniformMetric_costs_agree (M : StateDistance)
    (hmetric : IsStateMetric M) (hequivalent : UniformlyEquivalentToBures M)
    {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (rho : Op (Fin a × Fin b)) (hrho : IsDensityMatrix rho) :
    entanglementCost M rho = entanglementCost paperBures rho ∧
      alternativeCost M rho = alternativeCost paperBures rho ∧
      entanglementCost M rho = regularizedFormation rho ∧
      alternativeCost M rho = regularizedFormation rho := by sorry

end

end QAlgorithms.Papers.Independent.Dependency50.P42
