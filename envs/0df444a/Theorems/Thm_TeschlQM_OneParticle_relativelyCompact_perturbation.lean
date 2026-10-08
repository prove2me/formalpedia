-- Prove2me | Theorems.Thm_TeschlQM_OneParticle_relativelyCompact_perturbation
-- name    : TeschlQM.OneParticle.relativelyCompact_perturbation
-- status  : Open
-- author  : @Gabewhigham
-- created : 2026-10-07T15:19:51.763104+00:00
-- url     : https://prove2.me/theorems/1a5686e3-98b6-4a51-aa10-85eea41a41d8
-- title:
--   Relatively compact symmetric perturbations: Kato–Rellich plus Weyl
-- statement:
--   Let $\mathfrak H$ be a complex Hilbert space, let $A$ be self-adjoint and bounded from below, and let $K$ be symmetric and relatively compact with respect to $A$. Then:
--
--   - $\mathfrak D(A+K)=\mathfrak D(A)$;
--   - $A+K$ is self-adjoint and bounded from below;
--   - $\sigma_{ess}(A+K)=\sigma_{ess}(A)$;
--   - every core of $A$ is a core of $A+K$.
--
--   Proof outline: a relatively compact $K$ has $A$-bound $0$ (Lemma 6.22). Kato–Rellich (Theorem 6.4) then gives self-adjointness, the lower bound and the preservation of cores. Since $R_A(z)-R_{A+K}(z)=R_{A+K}(z)KR_A(z)$ is compact, Weyl's theorem (Theorem 6.19) gives equality of the essential spectra.
--
--   Here $\sigma_{ess}=\sigma\setminus\sigma_d$, where $\sigma_d$ is the set of isolated eigenvalues of finite multiplicity.
-- source:
--   Teschl, Mathematical Methods in Quantum Mechanics, AMS GSM 99, 2009, Lemma 6.22, Theorem 6.4, Theorem 6.19 and Lemma 6.23 (pp. 135–148), as combined in the proof of Theorem 10.2, p. 222

import Mathlib
import Definitions.Def_TeschlQM_Shared_resolventSet
import Definitions.Def_TeschlQM_OneParticle_essentialSpectrum
import Definitions.Def_TeschlQM_Shared_IsRelativelyCompact
import Definitions.Def_TeschlQM_OneParticle_IsBoundedBelow

namespace TeschlQM.OneParticle

open scoped InnerProductSpace

/-- Teschl, Lemma 6.22, Theorem 6.4 (Kato–Rellich) and Lemma 6.23 / Theorem 6.19 (Weyl), as used
in the proof of Theorem 10.2. Let `A` be self-adjoint and bounded below, and let `K` be symmetric
and relatively compact with respect to `A`. Then `A + K` has domain `𝔇(A)`, is self-adjoint and
bounded below, `σ_ess(A + K) = σ_ess(A)`, and every core of `A` is a core of `A + K`. -/
theorem relativelyCompact_perturbation {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (A K : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A)
    (hAbdd : IsBoundedBelow A)
    (hK : ∀ x y : K.domain, ⟪K x, (y : H)⟫_ℂ = ⟪(x : H), K y⟫_ℂ)
    (hrc : TeschlQM.Shared.IsRelativelyCompact K A) :
    (A + K).domain = A.domain ∧ IsSelfAdjoint (A + K) ∧ IsBoundedBelow (A + K) ∧
      essentialSpectrum (A + K) = essentialSpectrum A ∧
      ∀ S : Submodule ℂ H, A.HasCore S → (A + K).HasCore S := by sorry

end TeschlQM.OneParticle
