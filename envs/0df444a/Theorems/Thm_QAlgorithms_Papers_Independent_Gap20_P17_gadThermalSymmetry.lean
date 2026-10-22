-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap20_P17_gadThermalSymmetry
-- name    : QAlgorithms.Papers.Independent.Gap20.P17.gadThermalSymmetry
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T20:44:58.456157+00:00
-- url     : https://prove2.me/theorems/bc8c2aec-b840-42b2-a873-95b906483f19
-- title:
--   Thermal reflection symmetry of generalized amplitude damping
-- statement:
--   Let $\eta,\alpha\in[0,1]$. The physical generalized amplitude-damping channel $D_{\eta,\alpha}$ couples the input to a thermal qubit of excited population $\alpha$ by Eq.(10); equivalently it is $(1-\alpha)D_{\eta,0}+\alpha D_{\eta,1}$, where $D_{\eta,1}=XD_{\eta,0}(X\,\cdot\,X)X$ and $X$ is the bit flip. Then
--
--   $$D_{\eta,1-\alpha}(\rho)=XD_{\eta,\alpha}(X\rho X)X,\quad I_1(D_{\eta,\alpha})=I_1(D_{\eta,1-\alpha}),\quad R_1(D_{\eta,\alpha})=R_1(D_{\eta,1-\alpha}).$$
--
--   For each $p\in[0,1]$, $\operatorname{diag}(1-p,p)$ attains either entropy maximum for $\alpha$ if and only if $\operatorname{diag}(p,1-p)$ attains the corresponding maximum for $1-\alpha$. This symmetry permits restriction to the lower thermal half-interval.
-- source:
--   Reverse Coherent Information, arXiv:0808.0210v2, PDF p. 4, pp.3–4, Eq.(10) and thermal reflection paragraph

import Definitions.Def_QAlgorithms_Papers_Independent_Gap20_P17

noncomputable section

namespace QAlgorithms.Papers.Independent.Gap20.P17

open scoped Matrix ComplexConjugate

open Filter

open QAlgorithms.Papers.Independent.Information100.P67
  (IsIsometry receiverChannel complementaryChannel IsDegradable IsAntidegradable dilationPower)

open QAlgorithms.Papers.Independent.Dependency50.P09 (erasureFin entangledPhi tensorAction)

open QAlgorithms.Papers.Independent.Claimed50.P24 (productDilation)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF pp.3–4: thermal reflection alpha↔1-alpha conjugates the channel by X,
preserves both optimized entropy quantities, and reflects every optimal diagonal
population p to 1-p. The physical mixture weights correct the p.3 typo. -/
theorem gadThermalSymmetry (eta alpha : ℝ) (heta : eta ∈ Set.Icc (0 : ℝ) 1)
    (halpha : alpha ∈ Set.Icc (0 : ℝ) 1) :
    (let X : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]
     ∀ rho : Matrix (Fin 2) (Fin 2) ℂ,
       gadChannel eta (1-alpha) rho = X * gadChannel eta alpha (X*rho*X) * X) ∧
    forwardMaximum (gadDilation eta alpha) = forwardMaximum (gadDilation eta (1-alpha)) ∧
    reverseMaximum (gadDilation eta alpha) = reverseMaximum (gadDilation eta (1-alpha)) ∧
    (∀ p ∈ Set.Icc (0 : ℝ) 1,
      (forwardInfo (gadDilation eta alpha) (diagonalInput p) =
        forwardMaximum (gadDilation eta alpha) ↔
       forwardInfo (gadDilation eta (1-alpha)) (diagonalInput (1-p)) =
        forwardMaximum (gadDilation eta (1-alpha))) ∧
      (reverseInfo (gadDilation eta alpha) (diagonalInput p) =
        reverseMaximum (gadDilation eta alpha) ↔
       reverseInfo (gadDilation eta (1-alpha)) (diagonalInput (1-p)) =
        reverseMaximum (gadDilation eta (1-alpha)))) := by sorry

end QAlgorithms.Papers.Independent.Gap20.P17

end
