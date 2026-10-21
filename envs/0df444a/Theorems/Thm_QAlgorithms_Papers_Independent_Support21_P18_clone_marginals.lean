-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support21_P18_clone_marginals
-- name    : QAlgorithms.Papers.Independent.Support21.P18.clone_marginals
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T04:51:41.849143+00:00
-- url     : https://prove2.me/theorems/1b9f29d5-dfd3-4582-80cd-29dd99746016
-- title:
--   Clone marginals and their fidelity limit
-- statement:
--   Let $N,M\ge1$, let $\psi$ be a unit qubit vector, and write $\sigma=|\psi\rangle\langle\psi|$. In the explicit Eq. (7) joint output, each of the $N+M$ non-complement sites in registers $a,b$ has reduced density
--   $$
--   \rho_i=s_{NM}\sigma+\frac{1-s_{NM}}2I,
--   \qquad s_{NM}=\frac N{N+2}+\frac{2N}{(N+M)(N+2)}.
--   $$
--   Its cloning fidelity is $\operatorname{Tr}(\sigma\rho_i)=(1+s_{NM})/2$, which is strictly larger than $(N+1)/(N+2)$ for finite $M$. With $N$ fixed,
--   $$
--   \lim_{M\to\infty}\frac{1+s_{NM}}2=\frac{N+1}{N+2}.
--   $$
--   This quantifies the clone outputs of the NOT construction and their comparison with the measurement fidelity. Here $M$ counts additional clones, so there are $N+M$ clone sites.
-- source:
--   Optimal Manipulations with Qubits: Universal NOT Gate, arXiv:quant-ph/9901053v1, PDF p. 3, Quantum scenario, Eq.(9): remaining output qubits are clones with the stated shrinkage

import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P18

noncomputable section

namespace QAlgorithms.Papers.Independent.Support21.P18

open MeasureTheory Filter

open scoped ComplexConjugate Matrix ComplexOrder Matrix.Norms.L2Operator

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

/-- PDF p.3, Eq.(9): all N+M remaining qubits are clones with the printed 2N
numerator. Includes the strict finite-M fidelity comparison and the M-to-infinity
limit; cited optimal-cloning classification is not asserted as a new result. -/
theorem clone_marginals (N M : ℕ) (hN : 1 ≤ N) (hM : 1 ≤ M)
    (psi : EuclideanSpace ℂ (Fin 2)) (hpsi : IsState psi) :
    (∀ i : Fin (N + M),
      siteReduction (quantumClones N M psi) i = cloneOutput N M psi ∧
      effectProb (pureDensity psi) (siteReduction (quantumClones N M psi) i) =
        (1 + cloneShrink N M) / 2) ∧
    ((N : ℝ) + 1) / (N + 2) < (1 + cloneShrink N M) / 2 ∧
    Tendsto (fun m : ℕ => (1 + cloneShrink N m) / 2) atTop
      (nhds (((N : ℝ) + 1) / (N + 2))) := by sorry

end QAlgorithms.Papers.Independent.Support21.P18

end
