-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P15_eq41to43
-- name    : QAlgorithms.Papers.Independent.Support50.P15.eq41to43
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T19:46:33.159086+00:00
-- url     : https://prove2.me/theorems/7ccf95e7-32c7-4567-aa69-163153e24764
-- title:
--   eq41 43
-- statement:
--   Let $H$ be Hermitian in positive finite dimension, $T>0$, and $\rho_i$ a full-rank density matrix. Set $\rho_f=e^{-H/T}/\operatorname{tr}(e^{-H/T})$ and $F(\rho)=\operatorname{tr}(H\rho)-TS(\rho)$. For finite isothermal equilibration processes with fixed initial and final Hamiltonian $H$, compute heat $Q=\sum_j\operatorname{tr}[H_j(\rho_j-\rho_{j-1})]$ and extracted work $W=Q-\operatorname{tr}[H(\rho_f-\rho_i)]$. Then
--
--   $$\sup W=F(\rho_i)-F(\rho_f)=TD(\rho_i\|\rho_f)=-\operatorname{tr}[H(\rho_f-\rho_i)]+T[S(\rho_f)-S(\rho_i)].$$
--
--   This supremum is approached within every positive tolerance by actual finite equilibration processes. For any final state $\rho'$ and heat $Q'\le T[S(\rho')-S(\rho_i)]$, the corresponding work obeys $W'\le F(\rho_i)-F(\rho')=TD(\rho_i\|\rho_f)-TD(\rho'\|\rho_f)\le TD(\rho_i\|\rho_f)$. Free energy is uniquely minimized at $\rho_f$. This records approachable reversible work, without claiming a finite-process maximum.
-- source:
--   Tight bound on relative entropy by entropy difference, arXiv:1304.0036v3, PDF p. 13, eq41-43

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P15

noncomputable section

attribute [local instance] Classical.propDecidable

open scoped Matrix ComplexConjugate ENNReal Matrix.Norms.L2Operator

open Filter MeasureTheory

namespace QAlgorithms.Papers.Independent.Support50.P15

open QAlgorithms.Papers.Independent.Information100.P56 (entropy)

/-- Eqs. (41)--(43), PDF p.13. The process optimum is a supremum, approached to any epsilon;
work is computed from actual heat and the fixed-H internal energy change. -/
theorem eq41to43 {d : ℕ} (hd : 0 < d) (h : Matrix (Fin d) (Fin d) ℂ)
    (hh : h.IsHermitian) (t : ℝ) (ht : 0 < t) (a : EntropyState d) (ha : fullRank a.val) :
    ∃ hb : IsDensityMatrix (thermalFinite h t),
    let b : EntropyState d := ⟨thermalFinite h t, hb⟩
    let w := availableWork h t a
    ((t : EReal) * stateRelativeNats a b = (w : EReal)) ∧
    w = -(h * (b.val - a.val)).trace.re + t * difference b.val a.val ∧
    IsLUB {v | ∃ p : Process d, isIsothermal p h t a ∧ v = extractedWork p h} w ∧
    (∀ e > 0, ∃ p : Process d, isIsothermal p h t a ∧ w - e < extractedWork p h ∧ extractedWork p h ≤ w) ∧
    (∀ (r : EntropyState d) (q : ℝ), q ≤ t * difference r.val a.val →
      let w' := q - (h * (r.val - a.val)).trace.re
      w' ≤ helmholtzFreeEnergy h a.val t - helmholtzFreeEnergy h r.val t ∧
      ((helmholtzFreeEnergy h a.val t - helmholtzFreeEnergy h r.val t : ℝ) : EReal) =
        (t : EReal) * stateRelativeNats a b - (t : EReal) * stateRelativeNats r b ∧ w' ≤ w) ∧
    (∀ r : EntropyState d, helmholtzFreeEnergy h b.val t ≤ helmholtzFreeEnergy h r.val t ∧
      (helmholtzFreeEnergy h r.val t = helmholtzFreeEnergy h b.val t ↔ r = b)) := by sorry

end QAlgorithms.Papers.Independent.Support50.P15

end
