-- Prove2me | Theorems.Thm_PlantedIQP_lemma_40
-- name    : PlantedIQP.lemma_40
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T07:21:26.130053+00:00
-- url     : https://prove2.me/theorems/d11dcad4-1b92-4410-aa2b-79aa63c6f093
-- title:
--   Lemma 40 — vertex-cover decomposition of amplitudes
-- statement:
--   Let $f$ be a cubic polynomial and $C\subseteq[n]$ a vertex cover of its hypergraph $H(f)$. Then
--
--   1. for every $z\in\mathbb F_2^{C}$ the restricted polynomial $f^C_z(y)=f(x_C=z,\ x_{C^c}=y)$ has degree at most $2$ (it may have a constant term), and
--   2. for every $x\in\mathbb F_2^n$,
--
--   $$
--   a_f(x)=\frac1{2^{|C|}}\sum_{z\in\mathbb F_2^{|C|}}\mathrm{ngap}\big(f^C_z+\langle x_{C^c},\cdot\rangle\big)\,(-1)^{\langle x_C,z\rangle}.
--   $$
--
--   Since gaps of quadratic polynomials are computable in polynomial time, this reduces computing $a_f(x)$ to $2^{|C|}$ polynomial-time computations.
--
--   Differences from the source:
--   - reading: C ⊂ [n] → C ⊆ [n]; reason: the proof of Theorem 41 uses C = [h+1, …, n], all of [n] when h = 0
--   - reading: quadratic polynomials f^C_z specified in the proof → f^C_z(y) = f(x_C = z, x_{C^c} = y), with its degree ≤ 2 stated as a conclusion; reason: Eq. (50) of the proof defines f^C_z this way; the degree bound is the content of the lemma
--   - encoding: f^C_z ∈ 𝔽₂[x₁, …, x_{|C^c|}] → a function on 𝔽₂ indexed by the subtype {i ∉ C}; reason: same polynomial up to renaming the variables
-- source:
--   Bläser, Gullans, Hangleiter, Liu, Qiao, Verifiable quantum advantage based on polynomials with planted structures, arXiv:2609.39918 (sha256 6e261694…), Lemma 40, Eq. (49), p.25

import Mathlib
import Definitions.Def_PlantedIQP_IsVertexCover
import Definitions.Def_PlantedIQP_restrictCover
import Definitions.Def_PlantedIQP_amplitude
import Definitions.Def_PlantedIQP_mobiusCoeff

set_option autoImplicit false

namespace PlantedIQP

/-- Bläser, Gullans, Hangleiter, Liu, Qiao, *Verifiable quantum advantage based on polynomials with
planted structures*, arXiv:2609.39918 (sha256 6e261694…), Lemma 40, p.25, Eq. (49): for a cubic polynomial `f` and a vertex cover
`C ⊆ [n]` of `H(f)`, every `f^C_z(y) = f(x_C = z, x_{C^c} = y)` is a quadratic polynomial (degree at
most 2, constant term allowed), and for every `x`,
`a_f(x) = 2^{−|C|} Σ_{z∈𝔽₂^{|C|}} ngap(f^C_z + ⟨x_{C^c}, ·⟩) (−1)^{⟨x_C, z⟩}`. -/
theorem lemma_40 {n : ℕ} (f : CubicPoly n) (C : Finset (Fin n))
    (hC : IsVertexCover (polyHypergraph f) C) :
    (∀ z : {i // i ∈ C} → ZMod 2, DegLE (restrictCover f C z) 2) ∧
      ∀ x : Vec n, amp f x = (1 / (2 : ℝ) ^ C.card) *
        ∑ z : {i // i ∈ C} → ZMod 2,
          ngap (fun y => restrictCover f C z y + ∑ i : {i // i ∉ C}, x i.1 * y i) *
            (sgn (∑ i : {i // i ∈ C}, x i.1 * z i) : ℝ) := by sorry

end PlantedIQP
