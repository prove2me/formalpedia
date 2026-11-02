-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P57_single_edge_energy
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P57.single_edge_energy
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T06:13:25.956202+00:00
-- url     : https://prove2.me/theorems/8542d1c7-d0f3-41e4-8c5b-959586a7f130
-- title:
--   Static updates: one-edge energy is a quadratic form in a unit-modulus phase
-- statement:
--   Fix admissible RAGE data with $N,D\ge1$, nonzero raw MPS, a distinct pair $j,k$, and a Hermitian Hamiltonian $H$. Undo the final local rotations in $H$ and freeze all parameters except this edge. Remove its old phase from the pre-rotation vector and split the resulting vector into its $P_{11}$ and complementary components $v,u$. With $H_V=V^\dagger HV$, put $c_0=\langle u,H_Vu\rangle+\langle v,H_Vv\rangle$, $c_1=\langle u,H_Vv\rangle$, and $Z=\|M(A)\|^2$. For every $|z|=1$, the trial norm squared is $Z$ and
--
--   $$E(z)=\frac{c_0+2\operatorname{Re}(c_1z)}{Z}.$$
--
--   If $c_1\ne0$, $z_*=-\overline{c_1}/|c_1|$ minimizes this expression; if $c_1=0$, every unit-modulus phase is optimal. For a supplied sum of $m$ terms of fixed support at most $s$, scalar programs chosen before the numerical data compute $c_0,c_1,Z$ and the total energy in at most $C_s(m+1)ND^5$ operations. This is a single-edge optimum with a unit-circle constraint.
-- source:
--   Renormalization algorithm with graph enhancement, arXiv:0802.1211v1, PDF p. 3, Static updates: one-edge energy is a quadratic form in a unit-modulus phase

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P57

noncomputable section

open scoped ComplexConjugate Matrix

namespace QAlgorithms.Papers.Independent.Intakethird100.P57

attribute [local instance] Classical.propDecidable

/-- PDF p.3, Static updates: a constrained quadratic single-edge minimum, together
with exact coefficient and finite local-Hamiltonian evaluation. The coefficient calculation
costs O((m+1)ND⁵) for m terms of fixed support, using supports enlarged by the two edge sites.
This does not assert the source's separate, insufficiently specified O(D³) solve/sweep bounds. -/
theorem single_edge_energy :
    (∀ (N D : ℕ) (hN : 1 ≤ N) (hD : 1 ≤ D)
      (A : Tensors N D) (G : PhaseGraph N) (V : Fin N → Matrix.unitaryGroup Bool ℂ)
      (hv : traceMPS A ≠ 0) (j k : Fin N) (hjk : j ≠ k)
      (H : Matrix (Qubits N) (Qubits N) ℂ) (hH : H.IsHermitian),
      SingleEdgeEnergyLaw hN hD A G V hv j k hjk H hH) ∧
    (∀ s : ℕ, ∃ C : ℕ, 0 < C ∧
      ∃ programs : (N D m : ℕ) → (supports : Fin m → Finset (Fin N)) →
        Fin N → Fin N → EdgeProgram N D m supports,
      ∀ (N D m : ℕ) (supports : Fin m → Finset (Fin N)) (j k : Fin N),
        1 ≤ N → 1 ≤ D → j ≠ k → (∀ r, (supports r).card ≤ s) →
        let p := programs N D m supports j k
        p.scalar.calls = 0 ∧ p.scalar.work 0 ≤ C * (m + 1) * N * D ^ 5 ∧
        (∀ (A : Tensors N D) (G : PhaseGraph N) (V : Fin N → Matrix.unitaryGroup Bool ℂ)
          (terms : (r : Fin m) → Matrix (supports r → Bool) (supports r → Bool) ℂ),
          traceMPS A ≠ 0 → (∀ r, (terms r).IsHermitian) →
          let H := localTermHamiltonian supports terms
          let c := edgeCoefficients A G V j k H
          ∃ mem : ℕ → ℂ, p.scalar.execute (edgeData A G V terms) (fun _ => 0) = some mem ∧
            p.constantCoefficient < p.scalar.code.length ∧
            p.phaseCoefficient < p.scalar.code.length ∧ p.norm < p.scalar.code.length ∧
            p.totalEnergy < p.scalar.code.length ∧
            mem p.constantCoefficient = (c.1 : ℂ) ∧ mem p.phaseCoefficient = c.2 ∧
            mem p.norm = (‖traceMPS A‖ ^ 2 : ℝ) ∧
            mem p.totalEnergy = (rayleighEnergy H (rage A G V) : ℂ))) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P57

end
