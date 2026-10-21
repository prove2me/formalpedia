-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P29_direction_effective_channel
-- name    : QAlgorithms.Papers.Independent.Next46.P29.direction_effective_channel
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T14:24:45.819027+00:00
-- url     : https://prove2.me/theorems/18385c5f-7527-4b0a-92d2-7ae589021a26
-- title:
--   A bounded direction token induces dephasing followed by depolarization
-- statement:
--   Let $k=2j_R\ge0$ be an integer. The token is the highest-weight state $|j_R,j_R\rangle$ in the actual spin-$j_R$ representation, and the message is spin $1/2$ with $|0\rangle,|1\rangle$ of z-weights $+1/2,-1/2$. Let $\mathcal E_k$ be their correlated normalized SU(2) Haar encoding. Decode by the covariant token POVM of density $(k+1)|\Omega_{j_R}\rangle\langle\Omega_{j_R}|$ followed by the inverse qubit rotation, obtaining $\mathcal R_k$. The token is normalized, both maps are channels, and every qubit density operator satisfies
--
--   $$\mathcal R_k\mathcal E_k(\rho)=\frac{k}{k+2}\Delta(\rho)+\frac{2}{k+2}\frac{I_2}{2},\qquad\lim_{n\to\infty}\mathcal R_n\mathcal E_n(\rho)=\Delta(\rho).$$
--
--   Here $\Delta$ removes z-basis off-diagonal entries. The residual unknown rotation about z prevents recovery of transverse coherence, even in the limit. The fixed direction recovery also satisfies the separate §VI.B bound: for every deterministic CPTP decoder $\mathcal D$, $1-F_e(I_2/2,\mathcal R_k\mathcal E_k)\le 2[1-F_e(I_2/2,\mathcal D\mathcal E_k)]$, where $F_e$ is normalized entanglement fidelity. This is a fixed-token comparison at the maximally mixed input.
-- source:
--   Quantum communication using a bounded-size quantum reference frame, arXiv:0812.5040v2, PDF p. 15, §VI.A: direction-token effective decoherence, Eqs.(96)–(105)

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P29

noncomputable section

open MeasureTheory

open scoped Matrix ComplexConjugate ComplexOrder Manifold ContDiff Matrix.Norms.L2Operator

namespace QAlgorithms.Papers.Independent.Next46.P29

open QAlgorithms.Papers.Independent.Information100.P56 (IsIrreducible)

open QAlgorithms.Papers.Independent.Information100.P63 (mixed)

open QAlgorithms.Papers.Independent.Information100.P34 (dephasing)

open QAlgorithms.Papers.Independent.Information100.P71 (IsSubchannel)

attribute [local instance] Classical.decEq Classical.propDecidable

/-- PDF pp.15–16, Eqs.(96)–(105),(114): direction decoding first loses transverse
coherence, then shrinks the remaining z-component by `j_R/(j_R+1)`.
The formula includes `j_R=0` and all half-integer spins. The uniform-input
entanglement-infidelity bound is the separate approximate-reversal application
stated in §VI.B on p.16; it is not inherited from the canonical-token theorem. -/
theorem direction_effective_channel (k : ℕ) :
    IsState (directionKet k) ∧ IsChannel (directionEncoding k) ∧
    IsChannel (directionRecovery k) ∧
    (∀ D : Superop (Fin (k + 1) × Fin 2) (Fin 2), IsChannel D →
      1 - QuditFidelity.entanglementFidelity 2 (by decide)
          (directionRecovery k ∘ directionEncoding k) ≤
        2 * (1 - QuditFidelity.entanglementFidelity 2 (by decide)
          (D ∘ directionEncoding k))) ∧
    ∀ rho, IsDensityMatrix rho →
      directionRecovery k (directionEncoding k rho) =
        ((k : ℝ) / (k + 2) : ℂ) • dephasing rho +
        ((2 : ℝ) / (k + 2) : ℂ) • mixed (O := Fin 2) ∧
      Filter.Tendsto (fun n : ℕ => directionRecovery n (directionEncoding n rho))
        Filter.atTop (nhds (dephasing rho)) := by sorry

end QAlgorithms.Papers.Independent.Next46.P29

end
