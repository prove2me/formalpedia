-- Prove2me | Theorems.Thm_TeschlQM_Shared_isBoundedBelowBy_of_spectrum_ge
-- name    : TeschlQM.Shared.isBoundedBelowBy_of_spectrum_ge
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-11-12T09:11:12.304127+00:00
-- url     : https://prove2.me/theorems/9c81d13d-8bb4-43f9-9799-406a661f878b
-- title:
--   A self-adjoint operator with $\sigma(A)\subseteq[\lambda,\infty)$ satisfies $A\ge\lambda$
-- statement:
--   Let $A$ be a symmetric operator on a complex Hilbert space that is bounded below and has a real point in its resolvent set (so $A$ is self-adjoint). If every $z\in\sigma(A)$ is real with $z\ge\lambda$, then $A\ge\lambda$, i.e. $\langle\psi,A\psi\rangle\ge\lambda\|\psi\|^2$ on $D(A)$.
--
--   Role: turns $\lambda^{N-1}=\min\sigma(H^{(N-1)})$ into the operator inequality $H^{(N-1)}\ge\lambda^{N-1}$ used in the localization estimate.
-- source:
--   Teschl, Mathematical Methods in Quantum Mechanics, AMS GSM 99, 2009, https://www.mat.univie.ac.at/~gerald/ftp/book-schroe/, Section 3.3 (spectral theorem: for self-adjoint A, sigma(A) contained in [lambda,infinity) implies A >= lambda); used in the proof of Theorem 11.2, p. 243

import Mathlib
import Definitions.Def_TeschlQM_Shared_resolventSet
import Definitions.Def_TeschlQM_Shared_essentialSpectrum
import Definitions.Def_TeschlQM_Shared_IsBoundedBelowBy
import Definitions.Def_TeschlQM_Shared_IsSymmetric

namespace TeschlQM.Shared

theorem isBoundedBelowBy_of_spectrum_ge {H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (A : H →ₗ.[ℂ] H) (hA : TeschlQM.Shared.IsSymmetric A)
    (γ : ℝ) (hγ : TeschlQM.Shared.IsBoundedBelowBy A γ) (t : ℝ)
    (ht : (t : ℂ) ∈ TeschlQM.Shared.resolventSet A) (lam : ℝ)
    (hlam : ∀ z ∈ TeschlQM.Shared.spectrum A, z.im = 0 ∧ lam ≤ z.re) :
    TeschlQM.Shared.IsBoundedBelowBy A lam := by sorry

end TeschlQM.Shared
