-- Prove2me | Theorems.Thm_ShamirLLR_imported_lemma_2_2
-- name    : ShamirLLR.imported_lemma_2_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T08:27:13.233264+00:00
-- url     : https://prove2.me/theorems/a13a0bfd-a898-4416-b35b-c8882039e9e5
-- title:
--   Imported Lemma 2.2 — box Cauchy–Schwarz
-- statement:
--   Let $T$ be a nonempty finite index set and $A=\mathbb F_p^T$. For $H:A\to\mathbb C$ and $B_1,B_2,B_3:A^2\to\mathbb C$ with $\|B_j\|_\infty\le1$,
--   $$
--   \Bigl|\mathbb E_{z_1,z_2,z_3\in A}H(z_1+z_2+z_3)B_1(z_2,z_3)B_2(z_1,z_3)B_3(z_1,z_2)\Bigr|\le\|H\|_{U^3(A)} .
--   $$
--
--   This lets all selected perturbations contribute their small $U^3$ norms at once in Lemma 2.1.
--
--   Differences from the source: none.
-- source:
--   Hwang–Maji–Shkredov–Ye, Local Leakage Resilience of Multiplication-friendly Shamir Secret Sharing (manuscript, 2 Nov 2026; held version, sha256 fcd6871f…), Imported Lemma 2.2, Eq. (13), p.15 (PDF p.16) [GT10, Lemma B.2]

import Mathlib
import Definitions.Def_ShamirLLR_gowersU3

set_option autoImplicit false

namespace ShamirLLR

/-- **Imported Lemma 2.2 (Box Cauchy–Schwarz).** Let `T` be a nonempty finite index set and
`A = 𝔽_p^T`. For `H : A → ℂ` and `B₁, B₂, B₃ : A² → ℂ` with `‖B_j‖_∞ ≤ 1`,
`|𝔼_{z₁,z₂,z₃ ∈ A} H(z₁ + z₂ + z₃) B₁(z₂, z₃) B₂(z₁, z₃) B₃(z₁, z₂)| ≤ ‖H‖_{U³(A)}`.

Source: Hwang–Maji–Shkredov–Ye, manuscript of 2 Nov 2026 (held version, sha256 fcd6871f…),
Imported Lemma 2.2, Eq. (13), p.15 ([GT10, Lemma B.2]). -/
theorem imported_lemma_2_2 (p : ℕ) [Fact p.Prime] {T : Type} [Fintype T] [DecidableEq T]
    [Nonempty T] (H : (T → ZMod p) → ℂ) (B₁ B₂ B₃ : (T → ZMod p) × (T → ZMod p) → ℂ)
    (hB₁ : ∀ z, ‖B₁ z‖ ≤ 1) (hB₂ : ∀ z, ‖B₂ z‖ ≤ 1) (hB₃ : ∀ z, ‖B₃ z‖ ≤ 1) :
    ‖((Fintype.card (T → ZMod p) : ℂ) ^ 3)⁻¹ *
        ∑ z₁ : T → ZMod p, ∑ z₂ : T → ZMod p, ∑ z₃ : T → ZMod p,
          H (z₁ + z₂ + z₃) * B₁ (z₂, z₃) * B₂ (z₁, z₃) * B₃ (z₁, z₂)‖ ≤ gowersU3 H := by sorry

end ShamirLLR
