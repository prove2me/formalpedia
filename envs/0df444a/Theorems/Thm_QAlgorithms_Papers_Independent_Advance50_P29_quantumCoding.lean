-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P29_quantumCoding
-- name    : QAlgorithms.Papers.Independent.Advance50.P29.quantumCoding
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T22:02:59.576968+00:00
-- url     : https://prove2.me/theorems/0cf1d634-49fc-4e0e-8a5a-6e0e5190cb8a
-- title:
--   §2.2: quantum coding theorem; random-coding proof of the direct part
-- statement:
--   Let $Q$ and $Q^{\prime}$ be finite complex Hilbert spaces of positive dimensions $M$ and $D$. A density operator is positive semidefinite with trace one. All logarithms and entropies are in bits. Write $\pi=I_Q/M$. Let $\mathcal N$ be CPTP. For a nonzero code subspace $C\subset Q$ of dimension $K$, let $\pi_C=\Pi_C/K$. Write $F_e(C,\mathcal N)=\max_{\mathcal R}F_e(\pi_C,\mathcal R\circ\mathcal N)$, where $\mathcal R:B(Q^{\prime})\to B(Q)$ ranges over all CPTP recovery maps and state entanglement fidelity is squared and unconditional. The operational capacity $Q(\mathcal N)$ is the supremum of all real rates $R$ for which one sequence of nonzero codes $C_n\subset Q^{\otimes n}$, one for every positive integer $n$, has $\limsup_n n^{-1}\log_2\dim C_n\ge R$ and $F_e(C_n,\mathcal N^{\otimes n})\to1$. For a state $\rho$, put $I(\rho,\mathcal N)=S(\mathcal N(\rho))-S_e(\rho,\mathcal N)$, where $S$ is von Neumann entropy and $S_e$ is the entropy of the reference/output state after applying $\mathcal N$ to a purification of $\rho$. The full tensor powers allow arbitrary entangled inputs. The regularized sequence converges, and
--
--   $$
--   Q(\mathcal N)=I_r(\mathcal N)=\lim_{n\to\infty}\frac1n\max_{\rho\text{ on }Q^{\otimes n}} I(\rho,\mathcal N^{\otimes n}).
--   $$
--
--   This identifies operational quantum capacity with regularized coherent information. The converse is recalled from earlier work; this paper proves the direct direction.
-- source:
--   A random-coding based proof for the quantum coding theorem, arXiv:0712.2558v1, PDF p. 6, §2.2: quantum coding theorem; random-coding proof of the direct part

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

/-- PDF pp.6–7, §2.2: operational quantum coding theorem, including existence of the
regularizing limit. The converse is attributed there to [16,17]; §§4–8 prove the direct part. -/
theorem quantumCoding [Nonempty I] [Nonempty J] (N : Superop I J) (hN : IsChannel N) :
    Tendsto (blockCoherentMaximumRate N) atTop (nhds (regularizedInformation N)) ∧
    limsupCodeCapacity N = regularizedInformation N := by sorry

end QAlgorithms.Papers.Independent.Advance50.P29

end
