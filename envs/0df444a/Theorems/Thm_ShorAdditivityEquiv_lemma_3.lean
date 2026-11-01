-- Prove2me | Theorems.Thm_ShorAdditivityEquiv_lemma_3
-- name    : ShorAdditivityEquiv.lemma_3
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T15:28:30.285695+00:00
-- url     : https://prove2.me/theorems/b3173740-b5c7-4adb-b0b3-0dc80f88f52d
-- title:
--   Lemma 3, p. 14 — a linear $f$ is determined by its values and first derivatives at spanning unit vectors
-- statement:
--   Let $\{|v_i\rangle\}$ be a family of unit vectors spanning a finite-dimensional Hilbert space $\mathcal H$, and let $f(\rho)=\mathrm{Tr}\,\tau\rho$ and $f'(\rho)=\mathrm{Tr}\,\tau'\rho$ with $\tau,\tau'$ Hermitian. Suppose that for every $i$
--
--   1. $f(|v_i\rangle\langle v_i|)=f'(|v_i\rangle\langle v_i|)$, and
--   2. for every $|w\rangle$ orthogonal to $|v_i\rangle$, the first derivatives at $\epsilon=0$ of
--   $$
--   \epsilon\mapsto f\Big(\big(\sqrt{1-\epsilon^2}\,|v_i\rangle+\epsilon|w\rangle\big)\big(\sqrt{1-\epsilon^2}\,\langle v_i|+\epsilon\langle w|\big)\Big)
--   $$
--   and of the same expression with $f'$ coincide.
--
--   Then $\tau=\tau'$: "f is completely determined". Lemma 3 is used in §6 to conclude that the dual function of $N_1\otimes N_2$ is the sum of those of $N_1$ and $N_2$.
--
--   Differences from the source:
--   - reading: "f is completely determined" → two Hermitian τ, τ' whose functions agree in value and first derivative at all v_i are equal; reason: the proof fixes the representation f(ρ) = Tr τρ and concludes "thus determining the matrix τ"
--   - encoding: the limit lim_{ε→0} (1/ε)(f(|vi⟩⟨vi|) − f((√(1−ε²)|vi⟩ + ε|wi⟩)(…))) → deriv at 0 of ε ↦ Re Tr(τ |u_ε⟩⟨u_ε|), u_ε = √(1−ε²) v_i + ε w; reason: the quotient is minus this derivative, which exists for linear f; equal data either way. The source's |wi⟩ is the |w⟩ of "for all orthogonal |w⟩"
--   - encoding: a set of unit vectors |vi⟩ that span H → a family v : ι → EuclideanSpace ℂ H with ‖v i‖ = 1 and Submodule.span ℂ (Set.range v) = ⊤; reason: same objects
-- source:
--   Shor, Equivalence of Additivity Questions in Quantum Information Theory, arXiv:quant-ph/0305035v4, Lemma 3, p. 14

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Information

open QAlgorithms

namespace ShorAdditivityEquiv

/-- Shor, *Equivalence of Additivity Questions in Quantum Information Theory*, arXiv:quant-ph/0305035v4, Lemma 3, p.14: "Suppose that we have a set of unit vectors |vi⟩ that span a Hilbert space
H. If we are given the value of f at all the vectors |vi⟩ as well as the value of the first
derivative of f, lim_{ε→0} (1/ε)( f(|vi⟩⟨vi|) − f((√(1 − ε²)|vi⟩ + ε|wi⟩)(√(1 − ε²)⟨vi| + ε⟨wi|)) )
at all the vectors |vi⟩ and for all orthogonal |w⟩, then f is completely determined."

Read as: two functions `f(ρ) = Tr τρ` and `f'(ρ) = Tr τ'ρ` (`τ`, `τ'` Hermitian) that agree at
every `|vᵢ⟩⟨vᵢ|` and whose first derivatives along every curve
`ε ↦ (√(1−ε²)|vᵢ⟩ + ε|w⟩)(√(1−ε²)⟨vᵢ| + ε⟨w|)` with `⟨vᵢ|w⟩ = 0` agree at `ε = 0`, are equal:
`τ = τ'`.

**Formalization Note.** The proof's first line fixes the representation `f(ρ) = Tr τρ`, so
"completely determined" is read as uniqueness of the Hermitian `τ`. The family of unit vectors
is indexed by an arbitrary type `ι` and spans `H = ℂ^H` over `ℂ`. `ε` is real; the derivative is
`deriv` at `0` of a differentiable real function. The source's difference quotient
`(1/ε)(f(v) − f(v_ε))` is the negative of the derivative and its `|wᵢ⟩` is the `|w⟩` of "for all
orthogonal |w⟩"; neither affects which data are given. `w` ranges over all complex vectors
orthogonal to `vᵢ` (unnormalized, which only rescales the derivative). -/
theorem lemma_3 {H ι : Type} [Fintype H] [DecidableEq H] (v : ι → EuclideanSpace ℂ H)
    (hunit : ∀ i, ‖v i‖ = 1) (hspan : Submodule.span ℂ (Set.range v) = ⊤)
    (τ τ' : Matrix H H ℂ) (hτ : τ.IsHermitian) (hτ' : τ'.IsHermitian)
    (hval : ∀ i, (τ * pureDensity (v i)).trace.re = (τ' * pureDensity (v i)).trace.re)
    (hder : ∀ i, ∀ w : EuclideanSpace ℂ H, inner ℂ (v i) w = 0 →
      deriv (fun ε : ℝ =>
        (τ * pureDensity (((Real.sqrt (1 - ε ^ 2) : ℝ) : ℂ) • v i + ((ε : ℝ) : ℂ) • w)).trace.re) 0 =
      deriv (fun ε : ℝ =>
        (τ' * pureDensity (((Real.sqrt (1 - ε ^ 2) : ℝ) : ℂ) • v i + ((ε : ℝ) : ℂ) • w)).trace.re) 0) :
    τ = τ' := by sorry

end ShorAdditivityEquiv
