-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P08_conditional_deterministic_fidelity
-- name    : QAlgorithms.Papers.Independent.Extend50.P08.conditional_deterministic_fidelity
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T19:26:46.881804+00:00
-- url     : https://prove2.me/theorems/d7be3ff8-2543-400d-b811-b3fd0f84fab8
-- title:
--   Conditional fidelity and deterministic completion
-- statement:
--   Let $N\ge1$, $d\ge2$, and let the resource filter $O$ be either the identity or the canonical deterministic-optimal filter obtained from a nonnegative unit principal teleportation-matrix eigenvector. Use the physical SRM effects $\Pi_i$ and failure $\Delta$. The corresponding deterministic protocol uses the same resource and effects $\Pi_i+\Delta/N$. Both families are physical and minimal-PBT success $p$ is positive. Their conditional and unconditional entanglement fidelities obey
--
--   $$F=\frac{F_{\mathrm{det}}}{p}.$$
--
--   For the nonoptimized qubit resource,
--   $$F=\frac{2^{-(N+2)}\sum_{\alpha\vdash N-1}\left(\sum_{\mu\in\alpha}\sqrt{d_\mu m_\mu}\right)^2}{1-(N+2)/2^{N+1}}.$$
--
--   All diagrams in this specialization have height at most two. This uses (A10) as the unambiguous numerator of the source’s qubit specialization. Here $d_\lambda$ is the dimension of the actual symmetric-group Specht module labelled by $\lambda$, and $m_\lambda$ is its Schur–Weyl multiplicity for local dimension $d$ (with $d=2$ in the qubit case).
-- source:
--   Minimal Port-based Teleportation, arXiv:2111.05499v2, PDF p. 10, §III A, Eqs.(35)–(37): conditional fidelity versus completed deterministic PBT

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P08

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder Matrix.Norms.L2Operator

namespace QAlgorithms.Papers.Independent.Extend50.P08

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Eqs.(35)–(37), PDF pp.10–11: linked SRM protocols, including the
nonoptimized qubit specialization using the unambiguous numerator (A10), p.20. -/
theorem conditional_deterministic_fidelity (d N : ℕ) (hd : 2 ≤ d) (hN : 0 < N) :
    (∀ O : AliceMatrix d N,
      (O = 1 ∨ ∃ v : Schur.Partition d N → ℝ, IsPrincipal v ∧ O = deterministicFilter v) →
      IsPhysicalPBT O (minimalEffects d N) ∧ IsPhysicalPBT O (completedEffects d N) ∧
      0 < pbtSuccess O (minimalEffects d N) ∧
      conditionalFidelity (by omega) O (minimalEffects d N) =
        QuditFidelity.entanglementFidelity d (by omega)
          (successfulMap O (completedEffects d N)) / pbtSuccess O (minimalEffects d N)) ∧
    conditionalFidelity (by norm_num : 0 < 2) (1 : AliceMatrix 2 N) (minimalEffects 2 N) =
      bellDeterministicFormula 2 N / (1 - ((N : ℝ) + 2) / 2 ^ (N + 1)) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P08

end
