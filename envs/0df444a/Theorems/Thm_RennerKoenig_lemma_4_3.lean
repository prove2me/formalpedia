-- Prove2me | Theorems.Thm_RennerKoenig_lemma_4_3
-- name    : RennerKoenig.lemma_4_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:48:26.017784+00:00
-- url     : https://prove2.me/theorems/9aff91a6-5837-4e63-9b8d-7d6e1e200b11
-- title:
--   Lemma 4.3 — $d(F(Z)|\{F\}\otimes\rho)=E_F[d(F(Z)|\rho)]$
-- statement:
--   Let $Z$ be a random variable with range $\mathcal Z$, let $\rho$ be a random state, and let $F$ be a random function with domain $\mathcal Z$ and finite range, independent of $Z$ and $\rho$. Then
--
--   $$
--   d\big(F(Z)\,\big|\,\{F\}\otimes\rho\big)=E_F\big[d(F(Z)|\rho)\big].
--   $$
--
--   Publishing the hash function therefore costs nothing beyond averaging over it: the non-uniformity given $F$ is the mean of the non-uniformities for each fixed choice $f$ of $F$.
--
--   Differences from the source:
--   - reading: F independent of Z and ρ → F independent of the pair (Z, ρ); reason: the proof of Lemma 4.3 uses the joint form, and the reading as two separate conditions makes Theorem 4.1 false (Z uniform on two bits, a uniform on two bits, F(z) = a·z, ρ = {Z ⊕ a}: d = 1/2 against a bound of 2^(-3/2))
--   - encoding: E_F[g(F)] → ∑ over ω₀ of P(ω₀) g(F(ω₀)), with the inner quantity computed for the fixed function f = F(ω₀) over the whole space; reason: the expectation of a function of F on a discrete space; the proof of Lemma 4.3 fixes f in the same way
--   - encoding: random variable with range 𝒳 and U uniform on 𝒳 → finite type α as the range; reason: a uniform U exists only on a finite range, so d and D are defined only there
--   - encoding: classical register ℂ^|X| ⊗ H, with |x⟩⟨x| ⊗ T, on either side of the tensor product → Hilbert sum ℓ²(X, H), register always the outer factor, |x⟩⟨x| ⊗ T as block x T; reason: ℂ^|X| ⊗ H is ℓ²(X, H) by the basis |x⟩; the page itself swaps the factors (proof of Lemma 4.3)
--   - encoding: tr|·| → published nuclear norm traceNormValue; reason: equal on trace-class operators, and only differences of density operators are measured
-- source:
--   Renner–König, Universally Composable Privacy Amplification Against Quantum Adversaries, arXiv:quant-ph/0403133v2, Lemma 4.3, p.8

import Mathlib
import Definitions.Def_ScutaruFid_IsDensityOperator
import Definitions.Def_RennerKoenig_chosenBasis
import Definitions.Def_RennerKoenig_nonUnif
import Definitions.Def_RennerKoenig_IndepOf

namespace RennerKoenig

/-- **Lemma 4.3.** Renner–König, *Universally Composable Privacy Amplification Against Quantum Adversaries*,
arXiv:quant-ph/0403133v2, Lemma 4.3, p.8: `d(F(Z)|{F} ⊗ ρ) = E_F[d(F(Z)|ρ)]` for a random
function `F` independent of `Z` and `ρ`.

**Formalization Note** The expectation fixes `f = F(ω₀)` and computes `d(f(Z)|ρ)` over the whole
space, as the proof's identity `[{F(Z)} ⊗ ρ|F = f] = [{f(Z)} ⊗ ρ]` requires. "Independent of `Z` and
`ρ`" is independence of `F` from the pair `(Z, ρ)`. -/
theorem lemma_4_3 {Ω Z S : Type*} [Fintype S] {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (P : PMF Ω) (Zv : Ω → Z) (ρ : Ω → H →L[ℂ] H)
    (hρ : ∀ ω, ScutaruFid.IsDensityOperator (chosenBasis H) (ρ ω))
    (F : Ω → Z → S)
    (hind : IndepOf P F (fun ω => (Zv ω, ρ ω))) :
    nonUnif P (fun ω => F ω (Zv ω)) (withReg F ρ) =
      ∑' ω₀, (P ω₀).toReal * nonUnif P (fun ω => F ω₀ (Zv ω)) ρ := by sorry

end RennerKoenig
