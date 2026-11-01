-- Prove2me | Theorems.Thm_ProcessingNetworks_EntropyIneq_theorem_F_1
-- name    : ProcessingNetworks.EntropyIneq.theorem_F_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T13:28:40.747416+00:00
-- url     : https://prove2.me/theorems/640b5fab-6ed2-4044-a8f2-bcf8a3f2d62e
-- title:
--   Theorem F.1 — $Q^k\to0$ $\iff$ $\rho(Q)<1$ $\iff$ $(I-Q)^{-1}=\sum_k Q^k$
-- statement:
--   Let $Q$ be a $d\times d$ real matrix, with no further restriction. The following three statements are equivalent:
--
--   1. $Q$ is convergent, i.e. $Q^k\to0$ as $k\to\infty$;
--   2. $\rho(Q)<1$;
--   3. $I-Q$ is non-singular and
--
--   $$
--   (I-Q)^{-1}=\sum_{k=0}^{\infty}Q^k .
--   $$
--
--   The series in (c) is the Neumann series of $(I-Q)^{-1}$. In Section B.4 the theorem turns the assumption $\rho(P)<1$ into the existence of $(I-P')^{-1}$ and its expansion $\sum_k P'^k$ (B.13).
--
--   **Formalization Note** $\rho$ is the largest modulus of a complex eigenvalue. The series in (c) is the limit of its partial sums $\sum_{k<n}Q^k$ in the entrywise topology, and non-singularity is invertibility of $I-Q$.
--
--   Differences from the source:
--
--   - generalization: Q a d × d matrix with d ≥ 1 → any d : ℕ, including d = 0; reason: for d = 0 all three statements hold trivially; every d ≥ 1 is the source's statement
--   - encoding: ρ(Q) = max |λᵢ| over the eigenvalues → RobustToDynamics.specRadius Q, the supremum of the moduli of the points of the spectrum of Q over ℂ; reason: that spectrum is the set of complex eigenvalues, a finite set, so the supremum is the maximum
--   - encoding: (I − Q)⁻¹ = Σ_{k=0}^∞ Q^k → partial sums Σ_{k<n} Q^k tend to (1 − Q)⁻¹ entrywise, together with IsUnit (1 − Q); reason: the ordinary meaning of an infinite series; Matrix.inv is the true inverse under IsUnit
--   - encoding: Q^k → 0 as k → ∞ → Tendsto of Q ^ k to 0 in the entrywise topology of Matrix (Fin d) (Fin d) ℝ; reason: on a finite-dimensional space this is convergence in any matrix norm
-- source:
--   Dai & Harrison, Processing Networks (pre-publication draft 2020-4-2, spnbook.org), Appendix F, Theorem F.1, eq. (F.1), p.309 (PDF 325)

import Mathlib
import Definitions.Def_RobustToDynamics_specRadius
import Definitions.Def_ProcessingNetworks_EntropyIneq_IsConvergent

open Filter Topology

namespace ProcessingNetworks.EntropyIneq

/-- **Theorem F.1** (Dai & Harrison, *Processing Networks*, pre-publication draft 2020-4-2,
spnbook.org, Appendix F, Theorem F.1, eq. (F.1), p.309 (PDF 325)). Let `Q` be a `d × d` real matrix.
The following three statements are equivalent:
(a) `Q` is convergent (`Qᵏ → 0`);
(b) `ρ(Q) < 1`;
(c) `I − Q` is non-singular with `(I − Q)⁻¹ = Σ_{k=0}^∞ Qᵏ`.

**Formalization Note** No restriction on `Q` ("It is true without any further restrictions", p.309).
`ρ` is the published `RobustToDynamics.specRadius` (supremum of the moduli of the complex
eigenvalues, i.e. of the spectrum of `Q` over `ℂ`). In (c), non-singularity is
`IsUnit (1 - Q)` and the series is the limit of its partial sums `Σ_{k<n} Qᵏ` in the entrywise
topology; `(1 - Q)⁻¹` is `Matrix.inv`, the true inverse once `IsUnit (1 - Q)` holds. Any `d : ℕ` is
allowed; `d = 0` is a trivial extra case. -/
theorem theorem_F_1 {d : ℕ} (Q : Matrix (Fin d) (Fin d) ℝ) :
    List.TFAE [IsConvergent Q, RobustToDynamics.specRadius Q < 1,
      IsUnit (1 - Q) ∧
        Tendsto (fun n : ℕ => ∑ k ∈ Finset.range n, Q ^ k) atTop (𝓝 (1 - Q)⁻¹)] := by sorry

end ProcessingNetworks.EntropyIneq
