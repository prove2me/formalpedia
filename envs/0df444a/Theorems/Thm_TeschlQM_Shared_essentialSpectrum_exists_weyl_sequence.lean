-- Prove2me | Theorems.Thm_TeschlQM_Shared_essentialSpectrum_exists_weyl_sequence
-- name    : TeschlQM.Shared.essentialSpectrum_exists_weyl_sequence
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-11-12T09:10:07.172184+00:00
-- url     : https://prove2.me/theorems/098e36e1-7cad-4a4a-a4f5-c32b7249693d
-- title:
--   Weyl criterion: points of $\sigma_{ess}$ of a self-adjoint operator carry singular Weyl sequences
-- statement:
--   Let $A$ be a symmetric operator on a complex Hilbert space with a real point $t$ in its resolvent set (so $A$ is self-adjoint). If $z\in\sigma_{ess}(A)$, then $z$ is real and there is a singular Weyl sequence: unit vectors $\psi_n\in D(A)$ with $\psi_n\rightharpoonup0$ weakly and $\|(A-z)\psi_n\|\to0$.
--
--   Role: the abstract Weyl criterion used to test points of $\sigma_{ess}(H^{(N)})$ against the IMS lower bound.
-- source:
--   Teschl, Mathematical Methods in Quantum Mechanics, AMS GSM 99, 2009, https://www.mat.univie.ac.at/~gerald/ftp/book-schroe/, Section 6.4, Weyl's criterion for the essential spectrum of a self-adjoint operator; used in the proof of Theorem 11.2, p. 243

import Mathlib
import Definitions.Def_TeschlQM_Shared_resolventSet
import Definitions.Def_TeschlQM_Shared_essentialSpectrum
import Definitions.Def_TeschlQM_Shared_IsBoundedBelowBy
import Definitions.Def_TeschlQM_Shared_IsSymmetric
open MeasureTheory Filter

namespace TeschlQM.Shared

theorem essentialSpectrum_exists_weyl_sequence {H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (A : H →ₗ.[ℂ] H) (hA : TeschlQM.Shared.IsSymmetric A)
    (t : ℝ) (ht : (t : ℂ) ∈ TeschlQM.Shared.resolventSet A) (z : ℂ)
    (hz : z ∈ TeschlQM.Shared.essentialSpectrum A) :
    z.im = 0 ∧ ∃ ψ : ℕ → A.domain, (∀ n, ‖(ψ n : H)‖ = 1) ∧
      (∀ φ : H, Tendsto (fun n => inner ℂ φ (ψ n : H)) atTop (nhds 0)) ∧
      Tendsto (fun n => ‖A (ψ n) - z • (ψ n : H)‖) atTop (nhds 0) := by sorry

end TeschlQM.Shared
