-- Prove2me | Theorems.Thm_RennerKoenig_theorem_4_1
-- name    : RennerKoenig.theorem_4_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:48:47.472136+00:00
-- url     : https://prove2.me/theorems/25d51d54-39ec-4b94-af18-72c890d0cd77
-- title:
--   Theorem 4.1 — two-universal hashing gives a key within $\frac12 2^{-\frac12(S_2([\{Z\}\otimes\rho])-S_0([\rho])-s)}$ of ideal
-- statement:
--   Let $Z$ be a random variable with range $\mathcal Z$, let $\rho$ be a random state on a Hilbert space, and let $F$ be a two-universal function on $\mathcal Z$ with range $\mathcal S=\{0,1\}^s$ which is independent of $Z$ and $\rho$. Then
--
--   $$
--   d\big(F(Z)\,\big|\,\{F\}\otimes\rho\big)\le\frac12\,2^{-\frac12\left(S_2([\{Z\}\otimes\rho])-S_0([\rho])-s\right)}.
--   $$
--
--   The key $F(Z)$ is thus close in trace distance to a uniform key independent of everything the adversary holds, including the public choice of $F$. Because the trace distance cannot grow under further processing, the key is secure in the universally composable sense.
--
--   **Formalization Note** The Hilbert space, the discrete probability space, the range $\mathcal Z$ and $s\ge0$ are arbitrary.
--
--   Differences from the source:
--   - reading: F independent of Z and ρ → F independent of the pair (Z, ρ); reason: the proof of Lemma 4.3 uses the joint form, and the reading as two separate conditions makes Theorem 4.1 false (Z uniform on two bits, a uniform on two bits, F(z) = a·z, ρ = {Z ⊕ a}: d = 1/2 against a bound of 2^(-3/2))
--   - encoding: rank [ρ] and S₀([ρ]), possibly infinite → hypothesis that the range of [ρ] is finite-dimensional; reason: it excludes only rank [ρ] = ∞, where S₀([ρ]) = ∞ and the printed bound is +∞
--   - encoding: classical register ℂ^|X| ⊗ H, with |x⟩⟨x| ⊗ T, on either side of the tensor product → Hilbert sum ℓ²(X, H), register always the outer factor, |x⟩⟨x| ⊗ T as block x T; reason: ℂ^|X| ⊗ H is ℓ²(X, H) by the basis |x⟩; the page itself swaps the factors (proof of Lemma 4.3)
--   - encoding: tr|·| → published nuclear norm traceNormValue; reason: equal on trace-class operators, and only differences of density operators are measured
--   - encoding: tr → series over a chosen Hilbert basis; real part where the page treats the trace as a real number; reason: the trace of a trace-class operator is independent of the basis and is real on the self-adjoint operators involved
-- source:
--   Renner–König, Universally Composable Privacy Amplification Against Quantum Adversaries, arXiv:quant-ph/0403133v2, Theorem 4.1, p.8

import Mathlib
import Definitions.Def_ScutaruFid_IsDensityOperator
import Definitions.Def_RennerKoenig_chosenBasis
import Definitions.Def_RennerKoenig_nonUnif
import Definitions.Def_RennerKoenig_S0
import Definitions.Def_RennerKoenig_S2
import Definitions.Def_RennerKoenig_IsTwoUniversal
import Definitions.Def_RennerKoenig_IndepOf

namespace RennerKoenig

/-- **Theorem 4.1.** Renner–König, *Universally Composable Privacy Amplification Against Quantum Adversaries*,
arXiv:quant-ph/0403133v2, Theorem 4.1, p.8: let `Z` be a random variable with range `𝒵`, `ρ` a
random state, and `F` a two-universal function on `𝒵` with range `{0,1}ˢ`, independent of `Z` and
`ρ`. Then `d(F(Z)|{F} ⊗ ρ) ≤ ½ · 2^(−½ (S₂([{Z} ⊗ ρ]) − S₀([ρ]) − s))`.

**Formalization Note** `H` is any complex Hilbert space, `(Ω, P)` any discrete probability space,
`𝒵` any type, `s` any natural number. "Independent of `Z` and `ρ`" is independence of `F` from the
pair `(Z, ρ)`: with two separate conditions the statement is false. `hfin` excludes only
`rank [ρ] = ∞`, where `S₀([ρ]) = ∞` and the printed bound is `+∞`. -/
theorem theorem_4_1 {Ω Z : Type*} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (P : PMF Ω) (Zv : Ω → Z) (ρ : Ω → H →L[ℂ] H)
    (hρ : ∀ ω, ScutaruFid.IsDensityOperator (chosenBasis H) (ρ ω))
    (s : ℕ)
    (F : Ω → Z → (Fin s → Bool))
    (hF : IsTwoUniversal P F)
    (hind : IndepOf P F (fun ω => (Zv ω, ρ ω)))
    (hfin : FiniteDimensional ℂ (LinearMap.range ((avg P ρ : H →L[ℂ] H) : H →ₗ[ℂ] H))) :
    nonUnif P (fun ω => F ω (Zv ω)) (withReg F ρ) ≤
      (1 / 2 : ℝ) * (2 : ℝ) ^ (-(1 / 2 : ℝ) * (S2 (avg P (withReg Zv ρ)) - S0 (avg P ρ) - (s : ℝ))) := by sorry

end RennerKoenig
