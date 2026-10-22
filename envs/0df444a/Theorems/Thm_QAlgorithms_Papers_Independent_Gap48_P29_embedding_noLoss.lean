-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P29_embedding_noLoss
-- name    : QAlgorithms.Papers.Independent.Gap48.P29.embedding_noLoss
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T04:27:04.115969+00:00
-- url     : https://prove2.me/theorems/a118c12f-f9ed-4039-a05b-1d508e800955
-- title:
--   No-loss embedding of a quantum operation
-- statement:
--   Let $\rho$ be a density operator on a nonzero finite-dimensional complex Hilbert space. Let $\mathcal F$ and $\mathcal G$ be CP trace-nonincreasing maps for which $\mathcal F+\mathcal G$ is trace preserving. Then
--
--   $$F_e(\rho,\mathcal F+\mathcal G)=F_e(\rho,\mathcal F)+F_e(\rho,\mathcal G)\geq F_e(\rho,\mathcal F).$$
--
--   Thus embedding a trace-decreasing operation into a physical trace-preserving map cannot reduce its unrenormalized entanglement fidelity.
-- source:
--   On Quantum Fidelities and Channel Capacities, arXiv:quant-ph/9809010v1, PDF p. 9, Eqs.(86)–(87), continuing p.10

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P29

noncomputable section

namespace QAlgorithms.Papers.Independent.Gap48.P29

open QAlgorithms Filter

open scoped Matrix ComplexConjugate ComplexOrder Topology

open QAlgorithms.Papers.Independent.Information100.P07 (IsProjection)

open QAlgorithms.Papers.Independent.Information100.P67 (squaredFidelity)

/-- PDF pp.9--10, Eqs.(86)--(87): additive unrenormalized Fe and no loss under any
physical TP embedding of a CP TNI operation. -/
theorem embedding_noLoss {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
    (rho : Matrix I I ℂ) (hrho : IsDensityMatrix rho)
    (F G : Superop I I) (hF : TraceNonincreasingCPMap F) (hG : TraceNonincreasingCPMap G)
    (hphysical : IsChannel (fun X => F X + G X)) :
    fe rho (fun X => F X + G X) = fe rho F + fe rho G ∧
      fe rho F ≤ fe rho (fun X => F X + G X) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P29

end
