-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P42_entanglementCost_weakAdditivity
-- name    : QAlgorithms.Papers.Independent.Dependency50.P42.entanglementCost_weakAdditivity
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T16:55:35.312982+00:00
-- url     : https://prove2.me/theorems/c213301d-bc36-48f8-b05f-06e0e3872685
-- title:
--   Weak additivity of entanglement cost
-- statement:
--   Let $\rho$ be a positive semidefinite, trace-one operator on $\mathbb C^a\otimes\mathbb C^b$, with positive integers $a,b$. Every tensor power retains the bipartition $A^{\otimes n}:B^{\otimes n}$.
--
--   For density operators define the root fidelity $F(\tau,\omega)=\operatorname{Tr}\sqrt{\sqrt\tau\,\omega\sqrt\tau}$ and the paper-normalized Bures distance $D(\tau,\omega)=2\sqrt{1-F(\tau,\omega)}$.
--
--   The cost $E_c(\tau)$ is the infimum of real rates $E$ such that, for every $\epsilon,\delta>0$, there exist integers $m\ge0$, $n\ge1$ and a deterministic LOCC map $L$ for which $|E-m/n|\le\delta$ and $D(L(\Psi_-^{\otimes m}),\tau^{\otimes n})\le\epsilon$. Here $\Psi_-$ is the density matrix of $(|01\rangle-|10\rangle)/\sqrt2$. LOCC means finite adaptive local quantum operations with unrestricted two-way classical communication; outputs are averaged over all outcomes, and local ancillary systems may be introduced and discarded.
--
--   For every positive integer $k$,
--
--   $$E_c(\rho^{\otimes k})=kE_c(\rho).$$
--
--   This expresses additivity for repeated copies of a single state.
-- source:
--   The asymptotic entanglement cost of preparing a quantum state, arXiv:quant-ph/0008134v1, PDF p. 3, Lemma 1

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P42

namespace QAlgorithms.Papers.Independent.Dependency50.P42

open scoped Matrix ComplexConjugate ComplexOrder

open Information100.P21 (Op)

noncomputable section

/-- PDF p.3, Lemma 1: weak additivity under positive powers of one state.
The source proof's erroneous closure claim about LOCC is not assumed. -/
theorem entanglementCost_weakAdditivity {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (rho : Op (Fin a × Fin b)) (hrho : IsDensityMatrix rho) (k : ℕ) (hk : 0 < k) :
    entanglementCost paperBures (dimensionedPower rho k) =
      (k : ℝ) * entanglementCost paperBures rho := by sorry

end

end QAlgorithms.Papers.Independent.Dependency50.P42
