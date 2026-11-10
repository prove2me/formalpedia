-- Prove2me | Theorems.Thm_PPSLattice_lemma_3_3
-- name    : PPSLattice.lemma_3_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T22:34:33.603206+00:00
-- url     : https://prove2.me/theorems/570715f9-b488-4911-98ee-cc4aedb0fde4
-- title:
--   Lemma 3.3 — smudging: $e_2$ and $e_2+e_1$ are statistically close when $B_1/B_2$ is negligible
-- statement:
--   Let $B_1=B_1(\lambda)$ and $B_2=B_2(\lambda)$ be positive integers and let $e_1=e_1(\lambda)$ be an integer with $|e_1|\le B_1$. Let $e_2$ be uniform on $[-B_2,B_2]$. If $B_1/B_2$ is negligible in $\lambda$, then
--   $$\mathrm{SD}\bigl(e_2,\ e_2+e_1\bigr)\ \text{is negligible in }\lambda.$$
--
--   The smudging noise $\tilde{\mathbf e}$ of skEnc hides the accumulated error $\mathbf e^\top\mathbf H_{S,i^*}\mathbf G^{-1}(\mathbf P)$ in the proofs of Lemmas 4.18 and 4.27.
--
--   Differences from the source:
--   - encoding: e₁ ∈ [−B₁, B₁] a fixed integer → a sequence e₁(λ) with |e₁(λ)| ≤ B₁(λ); reason: the lemma is asymptotic in λ; all sequences together amount to the worst e₁ at each λ
--   - encoding: statistically indistinguishable (SD ≤ negl(λ) for large λ) → NoisyOWMPC.Negligible of the statistical distance; reason: same notion
-- source:
--   Goyal–Yadugiri, New Results in Adaptively-Secure Broadcast Encryption and Succinct Computational Secret Sharing from Standard Lattices, STOC 2027 submission (manuscript sha256 7f9c493f…), Lemma 3.3 (Smudging Lemma [AJL+12]), p.16

import Mathlib
import Definitions.Def_NoisyOWMPC_Negligible
import Definitions.Def_PPSLattice_unifInt
import Definitions.Def_PPSLattice_SD
set_option autoImplicit false

namespace PPSLattice

/-- **Lemma 3.3** (smudging). Let `B₁ = B₁(λ)` and `B₂ = B₂(λ)` be positive integers and `e₁ = e₁(λ)` an
integer with `|e₁| ≤ B₁`. If `B₁/B₂` is negligible, then the statistical distance between `e₂ ← [−B₂, B₂]`
(uniform) and `e₂ + e₁` is negligible.
Goyal–Yadugiri, *New Results in Adaptively-Secure Broadcast Encryption and Succinct Computational Secret Sharing from Standard Lattices*, STOC 2027 submission (manuscript sha256 7f9c493f…), Lemma 3.3 (Smudging Lemma [AJL+12]), p.16; statistical indistinguishability ≈s, §3, p.15.

**Formalization Note.** "`e₁` a fixed integer" is a sequence `e₁(λ) ∈ [−B₁(λ), B₁(λ)]`; quantifying over
all sequences is the same as bounding the worst `e₁` for each `λ`. -/
theorem lemma_3_3 (B1 B2 : ℕ → ℕ) (hB1 : ∀ lam, 0 < B1 lam) (hB2 : ∀ lam, 0 < B2 lam)
    (e1 : ℕ → ℤ) (he1 : ∀ lam, |e1 lam| ≤ (B1 lam : ℤ))
    (hneg : NoisyOWMPC.Negligible fun lam => (B1 lam : ℝ) / (B2 lam : ℝ)) :
    NoisyOWMPC.Negligible fun lam =>
      SD (unifInt (B2 lam)) ((unifInt (B2 lam)).map fun z => z + e1 lam) := by sorry

end PPSLattice
