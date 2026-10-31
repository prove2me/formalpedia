-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P33_temporalModes_factorization
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P33.temporalModes_factorization
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T05:06:21.309728+00:00
-- url     : https://prove2.me/theorems/7b763c56-ae4e-452a-8a67-aa74adef7af7
-- title:
--   Finite-window temporal modes factor into coherent packets and vacuum
-- statement:
--   In the ideal noiseless vacuum-input CW model, let $\kappa\ge0$, $T>0$, $\alpha\in\mathbb C$, and $\phi,\tau\in\mathbb R$. For a finite observation of $N$ packets define $\Psi_n(t)=T^{-1/2}$ when $|t-\tau-nT|<T/2$, and zero otherwise. These functions genuinely belong to $L^2(\mathbb R)$; their $L^2$ representatives are asserted, the observed $N$ packets are orthonormal, and they extend to a Hilbert basis.
--
--   Set $\beta=\sqrt\kappa\alpha e^{i\phi}$, and let $f_N=\sum_{n<N}\sqrt T\beta\Psi_n$, the finite-window displacement field. For every packet,
--
--   $$
--   \int\overline{\Psi_n(t)}\beta\,dt=\sqrt{\kappa T}\alpha e^{i\phi}.
--   $$
--
--   For observed packets this is also $\langle\Psi_n,f_N\rangle$. Every $L^2$ mode orthogonal to all observed packets has zero displacement. For any $g\in L^2(\mathbb R)$, the amplitude is the integrable projection $\langle g,f_N\rangle=\int\overline{g(t)}f_N(t)\,dt$. Any finite orthonormal selection of modes has a normalized full-Fock coherent product with precisely those amplitudes and their coherent coefficients. Appending orthonormal modes orthogonal to the rectangular packets therefore appends vacuum factors.
--
--   This is the finite-window meaning of the paper's factorization. Endpoints and translation do not affect $L^2$ vectors; no constant nonzero field on the whole real line is treated as square integrable.
-- source:
--   The Quantum State of a Propagating Laser Field, arXiv:quant-ph/0111157v1, PDF p. 3, IIB, Eqs.(7)–(12)

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P33

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakenext100.P33

open Filter MeasureTheory

open scoped Topology Matrix ComplexConjugate

attribute [local instance] Classical.propDecidable

open QAlgorithms.Papers.Independent.Dependency50.P39

-- Accepted scalar phase; positive exponential, differing only by commuting scalars.

open QAlgorithms.Papers.Independent.Information100.P75 (phase)

/-- arXiv:quant-ph/0111157v1, PDF p.3, Eqs.(7)–(12). Finite-window
rectangular modes are orthonormal and extend to a Hilbert basis. Projection of
the constructed constant field gives sqrt(kappa*T)*alpha*exp(i phi), while
every orthogonal mode is vacuum. The arbitrary-mode projection is the genuine
integral (10), and arbitrary finite mode selections have normalized coherent
factors. tau=z0/c absorbs the harmless spatial translation. -/
theorem temporalModes_factorization (kappa T tau : ℝ) (alpha : ℂ) (phi : ℝ)
    (hk : 0 ≤ kappa) (hT : 0 < T) (N : ℕ) :
    (∀ n, MemLp (packetFunction T tau n) 2 volume ∧
      (temporalPacket T tau n : ℝ → ℂ) =ᵐ[volume] packetFunction T tau n) ∧
    Orthonormal ℂ (fun i : Fin N => temporalPacket T tau i.val) ∧
    (∃ (J : Type) (b : HilbertBasis J ℂ TemporalSpace) (e : Fin N ↪ J),
      ∀ i, b (e i) = temporalPacket T tau i.val) ∧
    (∀ n, cwPacketAmplitude kappa T tau alpha phi n =
      (Real.sqrt (kappa * T) : ℂ) * alpha * phase phi) ∧
    (∀ i : Fin N, modeAmplitude (temporalPacket T tau i.val)
      (temporalField kappa T tau alpha phi N) =
        (Real.sqrt (kappa * T) : ℂ) * alpha * phase phi) ∧
    (∀ g : TemporalSpace, (∀ i : Fin N,
      inner (𝕜 := ℂ) g (temporalPacket T tau i.val) = 0) →
      modeAmplitude g (temporalField kappa T tau alpha phi N) = 0) ∧
    (∀ g : TemporalSpace,
      Integrable (fun t => star (g t) * temporalField kappa T tau alpha phi N t) volume ∧
      modeAmplitude g (temporalField kappa T tau alpha phi N) =
        ∫ t, star (g t) * temporalField kappa T tau alpha phi N t) ∧
    (∀ (D : ℕ) (modes : Fin D → TemporalSpace), Orthonormal ℂ modes →
      ‖finiteModeVector (temporalField kappa T tau alpha phi N) modes‖ = 1 ∧
      ∀ m, finiteModeVector (temporalField kappa T tau alpha phi N) modes m =
        ∏ j, coherentCoefficient
          (modeAmplitude (modes j) (temporalField kappa T tau alpha phi N)) (m j)) ∧
    (∀ (J : ℕ) (g : Fin J → TemporalSpace), Orthonormal ℂ g →
      (∀ (j : Fin J) (i : Fin N),
        inner (𝕜 := ℂ) (g j) (temporalPacket T tau i.val) = 0) →
      finiteModeVector (temporalField kappa T tau alpha phi N)
        (Fin.append (fun i : Fin N => temporalPacket T tau i.val) g) =
      packetCoherent (Fin.append
        (fun _ : Fin N => (Real.sqrt (kappa * T) : ℂ) * alpha * phase phi)
        (fun _ : Fin J => 0))) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P33

end
