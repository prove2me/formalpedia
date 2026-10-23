-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P29_entanglementFidelity_convex
-- name    : QAlgorithms.Papers.Independent.Gap48.P29.entanglementFidelity_convex
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-22T04:10:54.985232+00:00
-- url     : https://prove2.me/theorems/82100291-41f4-4266-8b1e-9cf56d5ec488
-- title:
--   Convexity of entanglement fidelity in the input state
-- statement:
--   Let $\rho$ and $\sigma$ be density operators on the same nonzero finite-dimensional complex Hilbert space, let $\mathcal E$ be a fixed completely positive trace-nonincreasing operation on that space, and let $0\leq\lambda\leq1$. Entanglement fidelity is unrenormalized: $F_e(\rho,\mathcal E)=\sum_a|\operatorname{tr}(E_a\rho)|^2$ for a Kraus representation of $\mathcal E$. Then
--
--   $$F_e(\lambda\rho+(1-\lambda)\sigma,\mathcal E)\leq\lambda F_e(\rho,\mathcal E)+(1-\lambda)F_e(\sigma,\mathcal E).$$
--
--   This expresses convexity in the input with the operation held fixed.
-- source:
--   On Quantum Fidelities and Channel Capacities, arXiv:quant-ph/9809010v1, PDF p. 4, Lemma 1, Eq.(24)

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P29

noncomputable section

namespace QAlgorithms.Papers.Independent.Gap48.P29

open QAlgorithms Filter

open scoped Matrix ComplexConjugate ComplexOrder Topology

open QAlgorithms.Papers.Independent.Information100.P07 (IsProjection)

open QAlgorithms.Papers.Independent.Information100.P67 (squaredFidelity)

/-- PDF p.4, Lemma 1, Eq.(24): convexity in the input with the operation fixed.
The operation is CP trace nonincreasing, as in p.2, Eqs.(1)--(2). -/
theorem entanglementFidelity_convex {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
    (rho sigma : Matrix I I ℂ) (hrho : IsDensityMatrix rho) (hsigma : IsDensityMatrix sigma)
    (E : Superop I I) (hE : TraceNonincreasingCPMap E) (lam : ℝ) (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1) :
    fe ((lam : ℂ) • rho + ((1 - lam : ℝ) : ℂ) • sigma) E ≤
      lam * fe rho E + (1 - lam) * fe sigma E := by sorry

end QAlgorithms.Papers.Independent.Gap48.P29

end
