-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P40_tenderMeasurement
-- name    : QAlgorithms.Papers.Independent.Claimed50.P40.tenderMeasurement
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T10:50:01.543364+00:00
-- url     : https://prove2.me/theorems/0f195a47-4dbd-4a34-9662-6145466c4805
-- title:
--   Tender measurement with and without the recorded outcome
-- statement:
--   Let $(\rho_a)_{a\in A}$ be normalized positive states on a finite-dimensional C*-algebra $\mathcal A$. The label set $A$ is arbitrary. Let $(D_b)_{b\in B}$ be a finite-outcome POVM in $\mathcal A$, and let $\phi:A\to B$. Suppose $\epsilon>0$ and $1-\operatorname{Tr}(\rho_aD_{\phi(a)})\le\epsilon$ for every $a$.
--
--   Using the positive square roots, define the two actual measurement operations
--   $$
--   \delta(\rho)=\sum_b\sqrt{D_b}\rho\sqrt{D_b},\qquad
--   \Delta(\rho)=\sum_b |b\rangle\langle b|\otimes\sqrt{D_b}\rho\sqrt{D_b}.
--   $$
--   For every $a\in A$,
--   $$
--   \|\rho_a-\delta(\rho_a)\|_1\le\sqrt{8\epsilon}+\epsilon,\qquad
--   \big\||\phi(a)\rangle\langle\phi(a)|\otimes\rho_a-\Delta(\rho_a)\big\|_1
--   \le\sqrt{8\epsilon}+\epsilon.
--   $$
--   The trace is intrinsic, and $\|T\|_1=\operatorname{Tr}\sqrt{T^*T}$ is unhalved. No restriction $\epsilon<1$, injectivity of $\phi$, or orthogonality of the states is assumed. The result bounds disturbance of the explicitly constructed square-root instrument.
-- source:
--   The Capacity of the Quantum Multiple Access Channel, arXiv:quant-ph/9807019v3, PDF p. 4, Lemma 7 (Tender measurement)

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P40

noncomputable section

open scoped BigOperators Matrix ComplexConjugate

namespace QAlgorithms.Papers.Independent.Claimed50.P40

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Lemma 7 (tender measurement), PDF p.4: the actual square-root operations satisfy
both unhalved trace-norm bounds. The radical covers 8*epsilon. No epsilon<1 guard. -/
theorem tenderMeasurement {A B : Type*} [Fintype B] [DecidableEq B] {d : ℕ}
    (block : Fin d → ℕ) (rho : A → Matrix (Fin d) (Fin d) ℂ)
    (hrho : ∀ a, IsDensityMatrix (rho a) ∧ InBlocks block (rho a))
    (D : B → Matrix (Fin d) (Fin d) ℂ) (hD : IsPOVM D)
    (hblock : ∀ b, InBlocks block (D b)) (phi : A → B)
    (epsilon : ℝ) (hepsilon : 0 < epsilon)
    (herror : ∀ a, 1 - effectProb (D (phi a)) (rho a) ≤ epsilon) :
    (∀ a, traceNorm (rho a - tenderOperation D (rho a)) ≤ Real.sqrt (8 * epsilon) + epsilon) ∧
    (∀ a, traceNorm (idealLabel (phi a) (rho a) - labelledOperation D (rho a)) ≤
      Real.sqrt (8 * epsilon) + epsilon) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P40

end
