-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P31_box_low_temperature_fermionic_advantage
-- name    : QAlgorithms.Papers.Independent.Advance50.P31.box_low_temperature_fermionic_advantage
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T13:11:16.318994+00:00
-- url     : https://prove2.me/theorems/ef3cb9d9-d3e4-4eec-b48c-4c663df541f7
-- title:
--   Low-temperature fermionic advantage in a continuum 3D box
-- statement:
--   Compare noiseless channels carrying massive, indistinguishable, noninteracting spinless bosons and fermions in the same three-dimensional box, in the continuum ideal-gas thermodynamic model. Fix positive finite volume $V$, mass $m$, reduced Planck constant $\hbar$, Boltzmann constant $k_B$, and mean particle number $N$. Use the common density
--
--   $$
--   \rho(\epsilon)=A\epsilon^{1/2},\qquad
--   A=\frac{V}{4\pi^2}\left(\frac{2m}{\hbar^2}\right)^{3/2},\quad \epsilon>0.
--   $$
--
--   At each positive $T$, compute the two classical thermodynamic capacities by integrating the Bose and Fermi occupation entropies in bits against this density, solving the two fugacities separately at the same $N$. Bose fugacity saturates at one below condensation; excess condensate number contributes no entropy in this continuum model. Then
--
--   $$
--   \exists T_0>0\;\forall T\in(0,T_0),\qquad C_b(T,N)<C_f(T,N).
--   $$
--
--   This retains the complete sufficiently-low-positive-temperature ordering supported by the source's $T^{3/2}$ versus $T$ discussion. It does not state an exact fixed finite-box discrete-spectrum limit or use the defective printed fermion coefficient. The statistical-mechanical low-temperature expansions are attributed to Pathria, Ref.[25].
-- source:
--   Capacities of noiseless quantum channels for massive indistinguishable particles: Bosons vs. fermions, arXiv:quant-ph/0512200v3, PDF p. 15, §X, 3D box comparison

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P31

noncomputable section

open MeasureTheory

open scoped ENNReal BigOperators

namespace QAlgorithms.Papers.Independent.Advance50.P31

open QAlgorithms.Papers.Independent.Dependency50.P13 (IsTraceClass operatorTrace)

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable {I : Type*} [Countable I]

/-- PDF p.15, Section X: sufficiently small POSITIVE temperatures in the continuum
3D box model. Density A*sqrt(energy) counts spinless states in the same volume,
with the same mass, hbar, kB, and positive mean N. The defective printed fermion
coefficient is not assumed or asserted. This is not a fixed discrete box limit. -/
theorem box_low_temperature_fermionic_advantage
    (V m hbar kB N : ℝ) (hV : 0 < V) (hm : 0 < m)
    (hhbar : 0 < hbar) (hkB : 0 < kB) (hN : 0 < N) :
    let A := V / (4 * Real.pi ^ 2) * (2 * m / hbar ^ 2) ^ (3 / 2 : ℝ)
    ∃ T0 : ℝ, 0 < T0 ∧ ∀ T : ℝ, 0 < T → T < T0 →
      thermodynamicCapacity false A (3 / 2) kB N T <
        thermodynamicCapacity true A (3 / 2) kB N T := by sorry

end QAlgorithms.Papers.Independent.Advance50.P31

end
