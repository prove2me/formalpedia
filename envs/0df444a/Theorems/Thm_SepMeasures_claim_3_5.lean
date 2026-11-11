-- Prove2me | Theorems.Thm_SepMeasures_claim_3_5
-- name    : SepMeasures.claim_3_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T09:10:30.748482+00:00
-- url     : https://prove2.me/theorems/eeba912e-9c20-451b-9666-b0362cc6b6c4
-- title:
--   Claim 3.5 — if $p_2+p_3>1$ and $-q_2-q_3>1$, every sign region of $H_1,H_2$ has red mass on one side of $K$ and blue mass on the other
-- statement:
--   This claim lives inside the proof of Theorem 3.3. Let $\mu,\nu$ be probability measures on $\mathbb R^d$ ($d\ge1$) and $H_1,H_2,H_3,K$ oriented hyperplanes, each of $\mu$- and $\nu$-measure $0$, satisfying the bisection identities of p.20,
--   $$\mathbb E_\mu[\sigma_{H_1}]=\mathbb E_\mu[\sigma_{H_2}]=\mathbb E_\mu[\sigma_{H_1}\sigma_{H_3}]=0,\qquad \mathbb E_\nu[\sigma_{H_1}]=\mathbb E_\nu[\sigma_{H_3}]=\mathbb E_\nu[\sigma_{H_1}\sigma_{H_2}]=0 .$$
--   Write $p_i=\mathbb E_\mu[\sigma_K\sigma_{H_i}]$ and $q_i=\mathbb E_\nu[\sigma_K\sigma_{H_i}]$, and suppose $p_2+p_3>1$ and $-q_2-q_3>1$. Then for all $a,b\in\{-1,+1\}$,
--   $$\mu\big(\sigma_{H_1}=a,\ \sigma_{H_2}=\sigma_K=b\big)>0,\qquad \nu\big(\sigma_{H_1}=a,\ \sigma_{H_2}=b,\ \sigma_K=-b\big)>0 .$$
--
--   In the plane the two inequalities cannot hold together: the conclusion would make a line $K$ meet all four open quadrants of two lines, and this contradiction is how the paper proves (8). The claim itself does not depend on the dimension.
--
--   Differences from the source:
--   - generalization: µ, ν on ℝ² (the claim is stated in the proof of Theorem 3.3) → µ, ν on ℝ^d for every d ≥ 1; reason: the claim's proof uses no planarity; d = 2 is the paper's case
--   - generalization: µ, ν absolutely continuous (𝒫²_bc), so every line is null → only the four hyperplanes H₁, H₂, H₃, K are assumed µ- and ν-null; reason: the proof uses only these null sets; absolutely continuous measures satisfy them
--   - generalization: H₁, H₂, H₃ chosen by Lemma 2.3; K a line with Φ_K > 1, oriented so that p₂, p₃ ≥ 0, from which (9) and (11) give p₂ + p₃ > 1 and −q₂ − q₃ > 1 → any hyperplanes with the six expectation identities of p.20 and any K with p₂ + p₃ > 1 and −q₂ − q₃ > 1; reason: the chosen lines satisfy these identities and the claim's proof uses only them and the two inequalities
--   - reading: ν(σ_{H₁} = a, σ_{H₂} = −σ_K = b) > 0 → ν {y | σ_{H₁} y = a ∧ σ_{H₂} y = b ∧ σ_K y = −b} > 0; reason: the chained equality means σ_{H₂} = b and −σ_K = b; this is the event E′_{a,b} of the proof, p.24
-- source:
--   Correa–Griesbach–Harb–Hommelsheim–Jlibene–Livanos–Solan, Separating Measures by Hyperplanes (manuscript, STOC 2027 submission, sha256 96a8692407ff1815980863f3baa9c5d7b90ba27e781ed19063306f67d26fa82f), Claim 3.5, p.23 (proof pp.23–24), in the proof of Theorem 3.3 (context pp.20–23)

import Mathlib
import Definitions.Def_SepMeasures_Hyp

open MeasureTheory

namespace SepMeasures

/-- Correa–Griesbach–Harb–Hommelsheim–Jlibene–Livanos–Solan, *Separating Measures by Hyperplanes*
(manuscript, sha256 96a86924…fa82f), Claim 3.5, p.23 (proof pp.23–24), in the context of
the proof of Theorem 3.3 (pp.20–23). Let `μ, ν` be probability measures and `H₁, H₂, H₃, K`
hyperplanes, each of `μ`- and `ν`-measure `0`, with the bisection identities of p.20,
`E_μ[σ_{H₁}] = E_μ[σ_{H₂}] = E_μ[σ_{H₁}σ_{H₃}] = 0` and
`E_ν[σ_{H₁}] = E_ν[σ_{H₃}] = E_ν[σ_{H₁}σ_{H₂}] = 0`.
Write `pᵢ = E_μ[σ_K σ_{Hᵢ}]`, `qᵢ = E_ν[σ_K σ_{Hᵢ}]`, and suppose `p₂ + p₃ > 1` and `−q₂ − q₃ > 1`
(p.23). Then for every `a, b ∈ {−1, +1}`,
`μ(σ_{H₁} = a, σ_{H₂} = σ_K = b) > 0` and `ν(σ_{H₁} = a, σ_{H₂} = −σ_K = b) > 0`.

**Formalization Note.** The proof's context is written out as hypotheses. The lines are only
assumed null (in the paper `μ, ν` are absolutely continuous, so every line is null). The claim
is stated in every dimension `d`: its proof does not use planarity, and in the plane its
hypotheses cannot all hold (that contradiction is how the paper proves (8)). The printed
`σ_{H₂} = −σ_K = b` means `σ_{H₂} = b` and `σ_K = −b`. -/
theorem claim_3_5 (d : ℕ) (hd : 1 ≤ d) (μ ν : Measure (E d))
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (H₁ H₂ H₃ K : Hyp d)
    (hμ₁ : μ H₁.set = 0) (hμ₂ : μ H₂.set = 0) (hμ₃ : μ H₃.set = 0) (hμK : μ K.set = 0)
    (hν₁ : ν H₁.set = 0) (hν₂ : ν H₂.set = 0) (hν₃ : ν H₃.set = 0) (hνK : ν K.set = 0)
    (bμ₁ : ∫ x, H₁.sign x ∂μ = 0) (bμ₂ : ∫ x, H₂.sign x ∂μ = 0)
    (bμ₁₃ : ∫ x, H₁.sign x * H₃.sign x ∂μ = 0)
    (bν₁ : ∫ y, H₁.sign y ∂ν = 0) (bν₃ : ∫ y, H₃.sign y ∂ν = 0)
    (bν₁₂ : ∫ y, H₁.sign y * H₂.sign y ∂ν = 0)
    (hp : 1 < (∫ x, K.sign x * H₂.sign x ∂μ) + ∫ x, K.sign x * H₃.sign x ∂μ)
    (hq : 1 < -(∫ y, K.sign y * H₂.sign y ∂ν) - ∫ y, K.sign y * H₃.sign y ∂ν) :
    ∀ a ∈ ({-1, 1} : Set ℝ), ∀ b ∈ ({-1, 1} : Set ℝ),
      0 < μ {x | H₁.sign x = a ∧ H₂.sign x = b ∧ K.sign x = b} ∧
      0 < ν {y | H₁.sign y = a ∧ H₂.sign y = b ∧ K.sign y = -b} := by sorry

end SepMeasures
