-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P18_noisy_singlet_fidelities
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P18.noisy_singlet_fidelities
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T04:23:51.310996+00:00
-- url     : https://prove2.me/theorems/dad10c68-9c3d-4ee7-a760-3be7403440d3
-- title:
--   Noisy-singlet fidelities
-- statement:
--   Let $d\ge1$, $0\le p\le1$, and $\rho_p=pP_++(1-p)I/d^2$, where $P_+$ is the normalized $d$-dimensional plus Bell projector. Write $F(\rho)=\operatorname{Tr}(P_+\rho)$ and let $f(\rho)$ be the squared survival probability, averaged over normalized Haar pure inputs, of the actual complete Bell measurement and correction teleportation protocol using $\rho$. Then $\rho_p$ is a density operator and
--
--   $$f(\rho_p)=p+\frac{1-p}{d},\quad \frac1d\le f(\rho_p)\le1,\qquad F(\rho_p)=p+\frac{1-p}{d^2},\quad \frac1{d^2}\le F(\rho_p)\le1,$$
--   $$f(\rho_p)=\frac{dF(\rho_p)+1}{d+1}.$$
--
--   When $d\ge2$, either fidelity uniquely determines $p$ within $[0,1]$. When $d=1$, every member of the family equals $P_+$. These identities connect the two fidelity conventions without confusing them with root fidelity.
-- source:
--   General teleportation channel, singlet fraction and quasi-distillation, arXiv:quant-ph/9807091v2, PDF p. 5, §III.B, eqs.(14)–(16): noisy-singlet fidelities

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P18

noncomputable section

open QAlgorithms MeasureTheory

open scoped Matrix ComplexConjugate ComplexOrder Matrix.Norms.L2Operator

namespace QAlgorithms.Papers.Independent.Intakenext100.P18

open QAlgorithms.Papers.Independent.Claimed50.P28 (maximallyEntangledDensity)

open QAlgorithms.Papers.Independent.Support50.P11 (choiState teleportWeyl bellKet)

open QAlgorithms.Papers.Independent.Renew46.P40 (initialJoint)

/-- PDF p.5, (14)--(16): original mixture range, both fidelities and both
bounds. Parameter uniqueness is asserted only in dimensions at least two. -/
theorem noisy_singlet_fidelities (d : ℕ) (hd : 0 < d) (p : ℝ)
    (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    IsDensityMatrix (noisySinglet d hd p) ∧
    QuditFidelity.averageFidelity d hd (standardTeleport d (noisySinglet d hd p)) =
      p + (1 - p) / d ∧
    1 / (d : ℝ) ≤ QuditFidelity.averageFidelity d hd (standardTeleport d (noisySinglet d hd p)) ∧
    QuditFidelity.averageFidelity d hd (standardTeleport d (noisySinglet d hd p)) ≤ 1 ∧
    effectProb (maximallyEntangledDensity d) (noisySinglet d hd p) = p + (1 - p) / (d : ℝ)^2 ∧
    1 / (d : ℝ)^2 ≤ effectProb (maximallyEntangledDensity d) (noisySinglet d hd p) ∧
    effectProb (maximallyEntangledDensity d) (noisySinglet d hd p) ≤ 1 ∧
    QuditFidelity.averageFidelity d hd (standardTeleport d (noisySinglet d hd p)) =
      ((d : ℝ) * effectProb (maximallyEntangledDensity d) (noisySinglet d hd p) + 1) / (d + 1 : ℝ) ∧
    (2 ≤ d → ∀ r : ℝ, 0 ≤ r → r ≤ 1 →
      (effectProb (maximallyEntangledDensity d) (noisySinglet d hd p) = effectProb (maximallyEntangledDensity d) (noisySinglet d hd r) → p = r) ∧
      (QuditFidelity.averageFidelity d hd (standardTeleport d (noisySinglet d hd p)) =
        QuditFidelity.averageFidelity d hd (standardTeleport d (noisySinglet d hd r)) → p = r)) ∧
    (d = 1 → ∀ r : ℝ, 0 ≤ r → r ≤ 1 → noisySinglet d hd r = maximallyEntangledDensity d) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P18

end
