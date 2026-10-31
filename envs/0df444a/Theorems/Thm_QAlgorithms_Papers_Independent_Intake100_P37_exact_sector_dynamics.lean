-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P37_exact_sector_dynamics
-- name    : QAlgorithms.Papers.Independent.Intake100.P37.exact_sector_dynamics
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T12:05:35.687776+00:00
-- url     : https://prove2.me/theorems/0618e964-b609-44c5-86a3-f9730465f84d
-- title:
--   Derived exact dynamics of the physical emission sectors
-- statement:
--   Let $A,m\ge0$ and $\gamma,t\in\mathbb R$. In the singlet five-mode convention, for $0\le l\le A$ define
--
--   $$
--   F_l=\binom{m+l+1}{l}^{-1/2}\sum_{i=0}^l(-1)^i\sqrt{\binom{m+l-i}{m}}
--   |m+l-i,i,i,l-i,A-l\rangle.
--   $$
--
--   These vectors are orthonormal. The physical five-mode Hamiltonian acts on their span by the derived tridiagonal matrix $K$ with $K_{l+1,l}=K_{l,l+1}=\gamma\sqrt{(l+1)(A-l)(m+l+2)}$ and all other entries zero. For every normalized polarization $\psi$, the rotated and physically embedded vectors $F_l(\psi)$ are orthonormal, the all-excited input is $F_0(\psi)$, and the actual full-sector exponential satisfies
--
--   $$
--   \Psi(t,\psi)=\sum_{l=0}^A f_l(t)F_l(\psi),\qquad f_l(t)=(e^{-itK})_{l0}.
--   $$
--
--   Thus the transfer dynamics is a conclusion about the physical Hamiltonian. Zero endpoints are implemented by the finite index set, so $A=0$ yields one stationary sector without invoking nonexistent neighboring states.
-- source:
--   Lambda's, V's and optimal cloning with stimulated emission, arXiv:quant-ph/0003025v1, PDF p. 5, Sec. II C, Eqs.(18)-(19),(21)

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P37

noncomputable section

namespace QAlgorithms.Papers.Independent.Intake100.P37

open QAlgorithms

open scoped Matrix ComplexOrder ComplexConjugate Matrix.Norms.L2Operator

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF p.5 Eqs.(18),(19),(21): normalized orthogonal physical sectors,
the derived transfer action, and exact physical evolution. The finite sum
includes both boundaries; A=0 yields H F0=0 and a stationary single sector. -/
theorem exact_sector_dynamics (A m : ℕ) (gamma t : ℝ) :
    Orthonormal ℂ (fun l : Fin (A + 1) => emissionSectorKet A m l.val) ∧
    (∀ l : Fin (A + 1), act (fiveH A m gamma) (emissionSectorKet A m l.val) =
      ∑ k : Fin (A + 1), emissionTransfer A m gamma k l • emissionSectorKet A m k.val) ∧
    (∀ psi : EuclideanSpace ℂ (Fin 2), IsState psi →
      IsState (physicalInput A m psi) ∧
      Orthonormal ℂ (fun l : Fin (A + 1) => physicalSector A m l.val psi) ∧
      physicalInput A m psi = physicalSector A m 0 psi ∧
      physicalOutput A m gamma t psi =
        ∑ l : Fin (A + 1), emissionAmplitude A m gamma t l • physicalSector A m l.val psi) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P37

end
