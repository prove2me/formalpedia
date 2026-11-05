-- Prove2me | Theorems.Thm_RennerKoenig_lemma_4_6
-- name    : RennerKoenig.lemma_4_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:48:36.066392+00:00
-- url     : https://prove2.me/theorems/62906f27-c514-4ce6-9168-f925ec1a4f9e
-- title:
--   Lemma 4.6 — closed form of $D(X|\rho)$
-- statement:
--   Let $X$ be a random variable with range $\mathcal X$ and let $\rho$ be a random state, with $\rho_x=[\rho|X=x]$ for $x\in\mathcal X$ and $P_X(x)=\Pr[X=x]$. Then
--
--   $$
--   D(X|\rho)=\operatorname{tr}\Big(\Big(\sum_{x\in\mathcal X}P_X(x)^2\rho_x^2\Big)-\frac1{|\mathcal X|}[\rho]^2\Big).
--   $$
--
--   This is the form of $D$ that can be averaged over the hash function in Lemma 4.7.
--
--   **Formalization Note** The statement is an equality of complex numbers, so it includes that the right side is real.
--
--   Differences from the source:
--   - encoding: random variable with range 𝒳 and U uniform on 𝒳 → finite type α as the range; reason: a uniform U exists only on a finite range, so d and D are defined only there
--   - encoding: ρ_x undefined when Pr[X = x] = 0 → cond gives 0 there; reason: the term carries the weight Pr[X = x] = 0, so its value never matters
--   - encoding: classical register ℂ^|X| ⊗ H, with |x⟩⟨x| ⊗ T, on either side of the tensor product → Hilbert sum ℓ²(X, H), register always the outer factor, |x⟩⟨x| ⊗ T as block x T; reason: ℂ^|X| ⊗ H is ℓ²(X, H) by the basis |x⟩; the page itself swaps the factors (proof of Lemma 4.3)
--   - encoding: tr → series over a chosen Hilbert basis; real part where the page treats the trace as a real number; reason: the trace of a trace-class operator is independent of the basis and is real on the self-adjoint operators involved
-- source:
--   Renner–König, Universally Composable Privacy Amplification Against Quantum Adversaries, arXiv:quant-ph/0403133v2, Lemma 4.6, p.9

import Mathlib
import Definitions.Def_ScutaruFid_IsDensityOperator
import Definitions.Def_RennerKoenig_chosenBasis
import Definitions.Def_RennerKoenig_hsNonUnif
import Definitions.Def_RennerKoenig_cond
import Definitions.Def_RennerKoenig_prob
import Definitions.Def_RennerKoenig_tr

namespace RennerKoenig

/-- **Lemma 4.6.** Renner–König, *Universally Composable Privacy Amplification Against Quantum Adversaries*,
arXiv:quant-ph/0403133v2, Lemma 4.6, p.9:
`D(X|ρ) = tr((∑ₓ P_X(x)² ρ_x²) − |X|⁻¹ [ρ]²)`, with `ρ_x := [ρ|X = x]`.

**Formalization Note** An identity of complex numbers, so it also says the right side is real.
`P_X(x) = Pr[X = x]`. On a null `x` the page's `ρ_x` is undefined; `cond` gives `0`, and the weight
is `0` as well. -/
theorem lemma_4_6 {Ω α : Type*} [Fintype α] {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (P : PMF Ω) (X : Ω → α) (ρ : Ω → H →L[ℂ] H)
    (hρ : ∀ ω, ScutaruFid.IsDensityOperator (chosenBasis H) (ρ ω)) :
    ((hsNonUnif P X ρ : ℝ) : ℂ) =
      tr ((∑ x, (((prob P {ω | X ω = x}) ^ 2 : ℝ) : ℂ) • (cond P ρ {ω | X ω = x} * cond P ρ {ω | X ω = x})) - ((Fintype.card α : ℂ)⁻¹) • (avg P ρ * avg P ρ)) := by sorry

end RennerKoenig
