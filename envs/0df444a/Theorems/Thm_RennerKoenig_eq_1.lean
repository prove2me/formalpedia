-- Prove2me | Theorems.Thm_RennerKoenig_eq_1
-- name    : RennerKoenig.eq_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:46:53.03956+00:00
-- url     : https://prove2.me/theorems/b4629a19-f7d8-4cdb-bb19-3a8efc593c25
-- title:
--   Eq. (1) — $[\rho\otimes\{X\}]=E_X[\rho_X\otimes|X\rangle\langle X|]$
-- statement:
--   Let $X$ be a random variable and $\rho$ a random state on a Hilbert space, and put $\rho_x=[\rho|X=x]$. Then
--
--   $$
--   [\rho\otimes\{X\}]=E_X\big[\rho_X\otimes|X\rangle\langle X|\big]=\sum_x\Pr[X=x]\ \rho_x\otimes|x\rangle\langle x|.
--   $$
--
--   This decomposition of a classical-quantum state into its conditional blocks underlies Lemmas 2.2 and 4.6.
--
--   **Formalization Note** $X$ may have any range. The sum is an unconditional sum in operator norm.
--
--   Differences from the source:
--   - encoding: classical register ℂ^|X| ⊗ H, with |x⟩⟨x| ⊗ T, on either side of the tensor product → Hilbert sum ℓ²(X, H), register always the outer factor, |x⟩⟨x| ⊗ T as block x T; reason: ℂ^|X| ⊗ H is ℓ²(X, H) by the basis |x⟩; the page itself swaps the factors (proof of Lemma 4.3)
--   - encoding: ρ_x undefined when Pr[X = x] = 0 → cond gives 0 there; reason: the term carries the weight Pr[X = x] = 0, so its value never matters
-- source:
--   Renner–König, Universally Composable Privacy Amplification Against Quantum Adversaries, arXiv:quant-ph/0403133v2, eq. (1), p.4

import Mathlib
import Definitions.Def_ScutaruFid_IsDensityOperator
import Definitions.Def_RennerKoenig_chosenBasis
import Definitions.Def_RennerKoenig_avg
import Definitions.Def_RennerKoenig_cond
import Definitions.Def_RennerKoenig_prob
import Definitions.Def_RennerKoenig_withReg

namespace RennerKoenig

/-- **Eq. (1).** Renner–König, *Universally Composable Privacy Amplification Against Quantum Adversaries*,
arXiv:quant-ph/0403133v2, eq. (1), p.4: `[ρ ⊗ {X}] = E_X[ρ_X ⊗ |X⟩⟨X|]`, with `ρ_x := [ρ|X = x]`.

**Formalization Note** The expectation is `∑ₓ Pr[X = x] (·)`, an unconditional sum in operator norm
over the range of `X`, which may be any type. -/
theorem eq_1 {Ω α : Type*} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (P : PMF Ω) (X : Ω → α) (ρ : Ω → H →L[ℂ] H)
    (hρ : ∀ ω, ScutaruFid.IsDensityOperator (chosenBasis H) (ρ ω)) :
    avg P (withReg X ρ) =
      ∑' x, ((prob P {ω | X ω = x} : ℝ) : ℂ) • block x (cond P ρ {ω | X ω = x}) := by sorry

end RennerKoenig
