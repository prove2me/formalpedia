-- Prove2me | Theorems.Thm_RennerKoenig_lemma_4_7
-- name    : RennerKoenig.lemma_4_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:48:46.607591+00:00
-- url     : https://prove2.me/theorems/f0048769-54b4-49c9-8681-e624163a1987
-- title:
--   Lemma 4.7 — $E_F[D(F(Z)|\rho)]\le 2^{-S_2([\{Z\}\otimes\rho])}$
-- statement:
--   Let $Z$ be a random variable with range $\mathcal Z$, let $\rho$ be a random state, and let $F$ be a two-universal function on $\mathcal Z$ with finite range, chosen independently of $Z$ and $\rho$. Then
--
--   $$
--   E_F\big[D(F(Z)|\rho)\big]\le2^{-S_2([\{Z\}\otimes\rho])}.
--   $$
--
--   This is the collision estimate of the proof: two-universality removes every off-diagonal term and leaves the purity of the joint state.
--
--   Differences from the source:
--   - reading: F independent of Z and ρ → F independent of the pair (Z, ρ); reason: the proof of Lemma 4.3 uses the joint form, and the reading as two separate conditions makes Theorem 4.1 false (Z uniform on two bits, a uniform on two bits, F(z) = a·z, ρ = {Z ⊕ a}: d = 1/2 against a bound of 2^(-3/2))
--   - encoding: E_F[g(F)] → ∑ over ω₀ of P(ω₀) g(F(ω₀)), with the inner quantity computed for the fixed function f = F(ω₀) over the whole space; reason: the expectation of a function of F on a discrete space; the proof of Lemma 4.3 fixes f in the same way
--   - encoding: random variable with range 𝒳 and U uniform on 𝒳 → finite type α as the range; reason: a uniform U exists only on a finite range, so d and D are defined only there
--   - encoding: classical register ℂ^|X| ⊗ H, with |x⟩⟨x| ⊗ T, on either side of the tensor product → Hilbert sum ℓ²(X, H), register always the outer factor, |x⟩⟨x| ⊗ T as block x T; reason: ℂ^|X| ⊗ H is ℓ²(X, H) by the basis |x⟩; the page itself swaps the factors (proof of Lemma 4.3)
--   - encoding: tr → series over a chosen Hilbert basis; real part where the page treats the trace as a real number; reason: the trace of a trace-class operator is independent of the basis and is real on the self-adjoint operators involved
-- source:
--   Renner–König, Universally Composable Privacy Amplification Against Quantum Adversaries, arXiv:quant-ph/0403133v2, Lemma 4.7, p.10

import Mathlib
import Definitions.Def_ScutaruFid_IsDensityOperator
import Definitions.Def_RennerKoenig_chosenBasis
import Definitions.Def_RennerKoenig_hsNonUnif
import Definitions.Def_RennerKoenig_S2
import Definitions.Def_RennerKoenig_IsTwoUniversal
import Definitions.Def_RennerKoenig_IndepOf

namespace RennerKoenig

/-- **Lemma 4.7.** Renner–König, *Universally Composable Privacy Amplification Against Quantum Adversaries*,
arXiv:quant-ph/0403133v2, Lemma 4.7, p.10: for a two-universal `F` on `Z` chosen independently of
`Z` and `ρ`, `E_F[D(F(Z)|ρ)] ≤ 2^(−S₂([{Z} ⊗ ρ]))`.

**Formalization Note** The expectation fixes `f = F(ω₀)`, as in Lemma 4.3. The range of `F` is any
finite type ("let `S` be the range of `F`"). Independence is from the pair `(Z, ρ)`. -/
theorem lemma_4_7 {Ω Z S : Type*} [Fintype S] {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (P : PMF Ω) (Zv : Ω → Z) (ρ : Ω → H →L[ℂ] H)
    (hρ : ∀ ω, ScutaruFid.IsDensityOperator (chosenBasis H) (ρ ω))
    (F : Ω → Z → S)
    (hF : IsTwoUniversal P F)
    (hind : IndepOf P F (fun ω => (Zv ω, ρ ω))) :
    ∑' ω₀, (P ω₀).toReal * hsNonUnif P (fun ω => F ω₀ (Zv ω)) ρ ≤
      (2 : ℝ) ^ (-S2 (avg P (withReg Zv ρ))) := by sorry

end RennerKoenig
