-- Prove2me | Theorems.Thm_RennerKoenig_lemma_4_5
-- name    : RennerKoenig.lemma_4_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:49:00.039776+00:00
-- url     : https://prove2.me/theorems/b5e03155-ca3e-402e-b641-518f65700b1e
-- title:
--   Lemma 4.5 — $d(X|\rho)\le\frac12 2^{S_0([\rho])/2}\sqrt{|\mathcal X|\,D(X|\rho)}$
-- statement:
--   Let $X$ be a random variable with range $\mathcal X$ and let $\rho$ be a random state. Then
--
--   $$
--   d(X|\rho)\le\frac12\,2^{\frac{S_0([\rho])}2}\sqrt{|\mathcal X|\cdot D(X|\rho)}.
--   $$
--
--   This moves the analysis from the non-uniformity $d$ to its Hilbert–Schmidt analogue $D$, at the price of the dimension factors $|\mathcal X|$ and $2^{S_0([\rho])}$.
--
--   Differences from the source:
--   - encoding: random variable with range 𝒳 and U uniform on 𝒳 → finite type α as the range; reason: a uniform U exists only on a finite range, so d and D are defined only there
--   - encoding: rank [ρ] and S₀([ρ]), possibly infinite → hypothesis that the range of [ρ] is finite-dimensional; reason: it excludes only rank [ρ] = ∞, where S₀([ρ]) = ∞ and the printed bound is +∞
--   - encoding: classical register ℂ^|X| ⊗ H, with |x⟩⟨x| ⊗ T, on either side of the tensor product → Hilbert sum ℓ²(X, H), register always the outer factor, |x⟩⟨x| ⊗ T as block x T; reason: ℂ^|X| ⊗ H is ℓ²(X, H) by the basis |x⟩; the page itself swaps the factors (proof of Lemma 4.3)
--   - encoding: tr|·| → published nuclear norm traceNormValue; reason: equal on trace-class operators, and only differences of density operators are measured
--   - encoding: tr → series over a chosen Hilbert basis; real part where the page treats the trace as a real number; reason: the trace of a trace-class operator is independent of the basis and is real on the self-adjoint operators involved
-- source:
--   Renner–König, Universally Composable Privacy Amplification Against Quantum Adversaries, arXiv:quant-ph/0403133v2, Lemma 4.5, p.9

import Mathlib
import Definitions.Def_ScutaruFid_IsDensityOperator
import Definitions.Def_RennerKoenig_chosenBasis
import Definitions.Def_RennerKoenig_nonUnif
import Definitions.Def_RennerKoenig_hsNonUnif
import Definitions.Def_RennerKoenig_S0

namespace RennerKoenig

/-- **Lemma 4.5.** Renner–König, *Universally Composable Privacy Amplification Against Quantum Adversaries*,
arXiv:quant-ph/0403133v2, Lemma 4.5, p.9: `d(X|ρ) ≤ ½ 2^(S₀([ρ])/2) √(|X| · D(X|ρ))`.

**Formalization Note** `hfin` excludes only `rank [ρ] = ∞`, where `S₀([ρ]) = ∞`. -/
theorem lemma_4_5 {Ω α : Type*} [Fintype α] {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (P : PMF Ω) (X : Ω → α) (ρ : Ω → H →L[ℂ] H)
    (hρ : ∀ ω, ScutaruFid.IsDensityOperator (chosenBasis H) (ρ ω))
    (hfin : FiniteDimensional ℂ (LinearMap.range ((avg P ρ : H →L[ℂ] H) : H →ₗ[ℂ] H))) :
    nonUnif P X ρ ≤
      (1 / 2 : ℝ) * (2 : ℝ) ^ (S0 (avg P ρ) / 2) * Real.sqrt ((Fintype.card α : ℝ) * hsNonUnif P X ρ) := by sorry

end RennerKoenig
