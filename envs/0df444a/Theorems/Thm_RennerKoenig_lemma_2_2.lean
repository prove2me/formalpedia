-- Prove2me | Theorems.Thm_RennerKoenig_lemma_2_2
-- name    : RennerKoenig.lemma_2_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:47:04.748931+00:00
-- url     : https://prove2.me/theorems/36aa3d89-30dc-4b54-92d0-cb578e4e2862
-- title:
--   Lemma 2.2 — trace distance of states with the same classical part
-- statement:
--   Let $X$ be a random variable and let $\rho,\sigma$ be random states on the same Hilbert space, with $\rho_x=[\rho|X=x]$ and $\sigma_x=[\sigma|X=x]$. Then
--
--   $$
--   \delta\big([\rho\otimes\{X\}],[\sigma\otimes\{X\}]\big)=E_X\big[\delta(\rho_X,\sigma_X)\big].
--   $$
--
--   So the trace distance of two states sharing a classical part is the average of the conditional distances, which is what reduces Lemma 4.3 to a fixed hash function.
--
--   **Formalization Note** $X$ may have any range, and $E_X$ is the sum over $x$ with weights $\Pr[X=x]$.
--
--   Differences from the source:
--   - encoding: classical register ℂ^|X| ⊗ H, with |x⟩⟨x| ⊗ T, on either side of the tensor product → Hilbert sum ℓ²(X, H), register always the outer factor, |x⟩⟨x| ⊗ T as block x T; reason: ℂ^|X| ⊗ H is ℓ²(X, H) by the basis |x⟩; the page itself swaps the factors (proof of Lemma 4.3)
--   - encoding: tr|·| → published nuclear norm traceNormValue; reason: equal on trace-class operators, and only differences of density operators are measured
--   - encoding: ρ_x undefined when Pr[X = x] = 0 → cond gives 0 there; reason: the term carries the weight Pr[X = x] = 0, so its value never matters
-- source:
--   Renner–König, Universally Composable Privacy Amplification Against Quantum Adversaries, arXiv:quant-ph/0403133v2, Lemma 2.2, p.5

import Mathlib
import Definitions.Def_ScutaruFid_IsDensityOperator
import Definitions.Def_RennerKoenig_chosenBasis
import Definitions.Def_RennerKoenig_avg
import Definitions.Def_RennerKoenig_cond
import Definitions.Def_RennerKoenig_prob
import Definitions.Def_RennerKoenig_withReg
import Definitions.Def_RennerKoenig_traceDist

namespace RennerKoenig

/-- **Lemma 2.2.** Renner–König, *Universally Composable Privacy Amplification Against Quantum Adversaries*,
arXiv:quant-ph/0403133v2, Lemma 2.2, p.5:
`δ([ρ ⊗ {X}], [σ ⊗ {X}]) = E_X[δ(ρ_X, σ_X)]`, with `ρ_x := [ρ|X = x]`, `σ_x := [σ|X = x]`.

**Formalization Note** `X` may have any range. On a null `x` the conditioned operators are `0` and
the weight is `0`. -/
theorem lemma_2_2 {Ω α : Type*} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (P : PMF Ω) (X : Ω → α) (ρ σ : Ω → H →L[ℂ] H)
    (hρ : ∀ ω, ScutaruFid.IsDensityOperator (chosenBasis H) (ρ ω))
    (hσ : ∀ ω, ScutaruFid.IsDensityOperator (chosenBasis H) (σ ω)) :
    traceDist (avg P (withReg X ρ)) (avg P (withReg X σ)) =
      ∑' x, prob P {ω | X ω = x} * traceDist (cond P ρ {ω | X ω = x}) (cond P σ {ω | X ω = x}) := by sorry

end RennerKoenig
