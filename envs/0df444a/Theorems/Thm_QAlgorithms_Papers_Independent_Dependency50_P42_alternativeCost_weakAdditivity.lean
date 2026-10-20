-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P42_alternativeCost_weakAdditivity
-- name    : QAlgorithms.Papers.Independent.Dependency50.P42.alternativeCost_weakAdditivity
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T16:58:25.991985+00:00
-- url     : https://prove2.me/theorems/7d28dd48-d677-4ea6-aa13-592810425f34
-- title:
--   Weak additivity of the alternative cost
-- statement:
--   Let $\rho$ be a positive semidefinite, trace-one operator on $\mathbb C^a\otimes\mathbb C^b$, with positive integers $a,b$. Every tensor power retains the bipartition $A^{\otimes n}:B^{\otimes n}$.
--
--   For density operators define the root fidelity $F(\tau,\omega)=\operatorname{Tr}\sqrt{\sqrt\tau\,\omega\sqrt\tau}$ and the paper-normalized Bures distance $D(\tau,\omega)=2\sqrt{1-F(\tau,\omega)}$.
--
--   The cost $E_c(\tau)$ is the infimum of real rates $E$ such that, for every $\epsilon,\delta>0$, there exist integers $m\ge0$, $n\ge1$ and a deterministic LOCC map $L$ for which $|E-m/n|\le\delta$ and $D(L(\Psi_-^{\otimes m}),\tau^{\otimes n})\le\epsilon$. Here $\Psi_-$ is the density matrix of $(|01\rangle-|10\rangle)/\sqrt2$. LOCC means finite adaptive local quantum operations with unrestricted two-way classical communication; outputs are averaged over all outcomes, and local ancillary systems may be introduced and discarded.
--
--   The alternative cost $E_{\mathrm{alt}}(\tau)$ is the infimum over rates obeying the same requirements except that, for each $\epsilon,\delta>0$, there must exist $N$ such that every integer $n>N$ has a suitable $m$ and LOCC map $L$. Both $m$ and $L$ may depend on $n$.
--
--   For every positive integer $k$,
--
--   $$E_{\mathrm{alt}}(\rho^{\otimes k})=kE_{\mathrm{alt}}(\rho).$$
--
--   This records the source assertion of additivity in the precise weak sense of Lemma 1.
-- source:
--   The asymptotic entanglement cost of preparing a quantum state, arXiv:quant-ph/0008134v1, PDF p. 5, Section III, paragraph after Eq.(21)

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P42

namespace QAlgorithms.Papers.Independent.Dependency50.P42

open scoped Matrix ComplexConjugate ComplexOrder

open Information100.P21 (Op)

noncomputable section

/-- PDF p.5, following Eq.(21): alternative cost is weakly additive in the
sense of Lemma 1, for positive powers of a single state. -/
theorem alternativeCost_weakAdditivity {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (rho : Op (Fin a × Fin b)) (hrho : IsDensityMatrix rho) (k : ℕ) (hk : 0 < k) :
    alternativeCost paperBures (dimensionedPower rho k) =
      (k : ℝ) * alternativeCost paperBures rho := by sorry

end

end QAlgorithms.Papers.Independent.Dependency50.P42
