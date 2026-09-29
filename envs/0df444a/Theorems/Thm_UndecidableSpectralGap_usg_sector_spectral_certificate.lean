-- Prove2me | Theorems.Thm_UndecidableSpectralGap_usg_sector_spectral_certificate
-- name    : UndecidableSpectralGap.usg_sector_spectral_certificate
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-09-21T20:18:11.759407+00:00
-- url     : https://prove2.me/theorems/449a062a-bfef-4eed-a951-9fd6dec05605
-- title:
--   Section 6.2 — finite-volume sector spectral certificate
-- statement:
--   For each partial recursive code and each positive perturbation bound, construct the fixed matrices, projector and coefficients with exactly the arithmetic and norm constraints of Theorem 3. For each input, the resulting finite-volume spectra admit an energy sequence $E_L$ and auxiliary sets $S_L$ which eventually approximate every point of $[0,1]$ to any prescribed accuracy. Beyond one threshold, the spectrum contains both $0$ and $E_L$, is bounded below by $\min(0,E_L)$, and contains $E_L+S_L$. If $E_L\ge1$, zero has multiplicity one and every other spectral point is at least one. Halting implies $E_L\ge1$ eventually; non-halting implies $E_L\le0$ eventually.
--
--   This certificate isolates the finite-volume construction from the thermodynamic-limit argument. It is an open auxiliary obligation, not a proof of the construction.
-- source:
--   Cubitt, Pérez-García and Wolf, https://arxiv.org/pdf/1502.04573v5, Section 6.2, pp. 140–142, construction (130), spectral relations (131)–(132), using Corollary 54. Auxiliary consequence of the construction, with all finite-size assertions restricted to sufficiently large lattices.

import Definitions.Def_usg_spectral_notions

set_option autoImplicit false
open scoped ComplexOrder

namespace UndecidableSpectralGap

theorem usg_sector_spectral_certificate (u : Nat.Partrec.Code) (ε : ℝ) (hε : 0 < ε) :
    ∃ (d : ℕ) (A A' B C D D' : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)
      (Pi : Matrix (Fin d) (Fin d) ℂ) (β : ℚ) (α : ℕ → ℝ),
      -- `β` is a rational number, as small as desired
      0 < β ∧ (β : ℝ) < ε ∧
      -- (i) `A` is diagonal with integer entries
      (∀ i j, i ≠ j → A i j = 0) ∧ (∀ i, ∃ a : ℤ, A i i = (a : ℂ)) ∧
      -- (ii) `A'` is Hermitian with entries in `ℤ + (1/√2) ℤ`
      A'.IsHermitian ∧
        (∀ i j, ∃ a b : ℤ, A' i j = (a : ℂ) + (b : ℂ) / ((Real.sqrt 2 : ℝ) : ℂ)) ∧
      -- (iii) `B`, `C` have integer entries
      (∀ i j, ∃ a : ℤ, B i j = (a : ℂ)) ∧ (∀ i j, ∃ a : ℤ, C i j = (a : ℂ)) ∧
      -- (iv) `D` is diagonal with integer entries
      (∀ i j, i ≠ j → D i j = 0) ∧ (∀ i, ∃ a : ℤ, D i i = (a : ℂ)) ∧
      -- (v) `D'` is Hermitian with integer entries
      D'.IsHermitian ∧ (∀ i j, ∃ a : ℤ, D' i j = (a : ℂ)) ∧
      -- `Π` is a diagonal projector
      Pi.IsHermitian ∧ (∀ i j, i ≠ j → Pi i j = 0) ∧ Pi * Pi = Pi ∧
      -- `α(n)` is an algebraic number bounded by `2β`
      (∀ n, IsAlgebraic ℚ (α n) ∧ α n ≤ 2 * (β : ℝ)) ∧
      ∀ n : ℕ, ∀ (h1 : Matrix (Fin d) (Fin d) ℂ)
        (hrow hcol : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ),
        h1 = ((α n : ℝ) : ℂ) • Pi →
        hcol = D + ((β : ℝ) : ℂ) • D' →
        hrow = A + ((β : ℝ) : ℂ) •
          (A' + Complex.exp (Complex.I * (Real.pi : ℂ) * ((phi n : ℚ) : ℂ)) • B
            + Complex.exp (-(Complex.I * (Real.pi : ℂ) * ((phi n : ℚ) : ℂ))) • B.conjTranspose
            + Complex.exp (Complex.I * (Real.pi : ℂ) * (2 : ℂ) ^ (-(phiLen n : ℤ))) • C
            + Complex.exp (-(Complex.I * (Real.pi : ℂ) * (2 : ℂ) ^ (-(phiLen n : ℤ)))) • C.conjTranspose) →
        -- (i) the local interaction strength is bounded by 1
        localInteractionStrength h1 hrow hcol ≤ 1 ∧
        ∃ (E : ℕ → ℝ) (S : ℕ → Set ℝ) (L0 : ℕ),
          (∀ δ : ℝ, 0 < δ → ∃ N : ℕ, ∀ L > N,
            ∀ x ∈ Set.Icc (0 : ℝ) 1, ∃ s ∈ S L, |x - s| ≤ δ) ∧
          (∀ L > L0,
            (0 ∈ specReal (latticeHam L d h1 hrow hcol) ∧
             E L ∈ specReal (latticeHam L d h1 hrow hcol) ∧
             ∀ μ ∈ specReal (latticeHam L d h1 hrow hcol), min 0 (E L) ≤ μ) ∧
            (∀ s ∈ S L, E L + s ∈ specReal (latticeHam L d h1 hrow hcol)) ∧
            (1 ≤ E L → eigMultiplicity (latticeHam L d h1 hrow hcol) 0 = 1 ∧
              ∀ μ ∈ specReal (latticeHam L d h1 hrow hcol), μ ≠ 0 → 1 ≤ μ)) ∧
          ((u.eval n).Dom → ∀ L > L0, 1 ≤ E L) ∧
          (¬ (u.eval n).Dom → ∀ L > L0, E L ≤ 0) := by sorry

end UndecidableSpectralGap
