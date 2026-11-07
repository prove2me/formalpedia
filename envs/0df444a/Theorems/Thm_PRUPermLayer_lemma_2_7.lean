-- Prove2me | Theorems.Thm_PRUPermLayer_lemma_2_7
-- name    : PRUPermLayer.lemma_2_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T07:27:34.138664+00:00
-- url     : https://prove2.me/theorems/4416348a-1376-4860-bace-edeb09c3cf3e
-- title:
--   Lemma 2.7 — Haar collision probability $\frac{2}{N+1}\mathrm{Tr}((\Pi_{\mathrm{sym}}\otimes I)\rho)$
-- statement:
--   Let $N = 2^n$ and let $\rho$ be a state on two $n$-qubit registers and a reference register. If $U$ is Haar-random, the probability that measuring $(U\otimes U)\rho(U\otimes U)^\dagger$ in the computational basis gives equal outcomes on the two registers is
--   $$
--   \frac{2}{N+1}\,\mathrm{Tr}\big((\Pi_{\mathrm{sym}}\otimes I)\rho\big),
--   $$
--   where $\Pi_{\mathrm{sym}}$ projects onto the symmetric subspace of the two registers. In particular it is at most $2/(N+1)$, with equality exactly when the two registers are supported on the symmetric subspace.
--
--   It gives the Haar side of the collision test. All three clauses are stated.
--
--   Differences from the source:
--   - encoding: the probability of equal outcomes → $\mathbb E_U \mathrm{Tr}((\Pi_{\mathrm{eq}}\otimes I)(U\otimes U\otimes I)\rho(U\otimes U\otimes I)^\dagger)$ (real part); reason: Born rule; same number
--   - encoding: the two registers are supported on the symmetric subspace → $(\Pi_{\mathrm{sym}}\otimes I)\rho = \rho$; reason: for a state these are the same condition
--   - encoding: a reference register → a reference register of any finite type $R$; reason: same objects
-- source:
--   Shen–Zhong, Pseudorandom Unitaries from a Random Permutation and One Layer of Single-Qubit Gates, manuscript (STOC 2027 submission; held version sha256 395fcfa3…5bcb), Lemma 2.7, p.11 (PDF p.13)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Information
import Definitions.Def_PRUPermLayer_haar
import Definitions.Def_PRUPermLayer_piEqTwo
import Definitions.Def_PRUPermLayer_piSym
open MeasureTheory
open scoped ComplexOrder Matrix

namespace PRUPermLayer

/-- **Lemma 2.7** (Shen–Zhong, *Pseudorandom Unitaries from a Random Permutation and One Layer of Single-Qubit Gates*, manuscript (STOC 2027 submission; held version sha256 395fcfa3…5bcb), Lemma 2.7, p.11 (PDF p.13)). Let `ρ` be a state on two `n`-qubit
registers and a reference. If `U` is Haar-random, the probability that measuring
`(U ⊗ U)ρ(U ⊗ U)†` in the computational basis gives equal outcomes on the two registers is
`(2/(N + 1)) Tr((Π_sym ⊗ I)ρ)`, where `Π_sym` projects onto the symmetric subspace of the two
registers. In particular it is at most `2/(N + 1)`, with equality exactly when the two registers
are supported on the symmetric subspace.

**Formalization Note** `N = 2ⁿ`; the reference register is any finite type `R`; `U ⊗ U` acts on
the two registers and the identity on `R`. The probability of equal outcomes is
`Tr((Π_eq ⊗ I)(U ⊗ U ⊗ I)ρ(U ⊗ U ⊗ I)†)`. "Supported on the symmetric subspace" is
`(Π_sym ⊗ I)ρ = ρ`. All three clauses are stated. -/
theorem lemma_2_7 (n : ℕ) {R : Type*} [Fintype R] [DecidableEq R]
    (ρ : Matrix ((Fin (2 ^ n) × Fin (2 ^ n)) × R) ((Fin (2 ^ n) × Fin (2 ^ n)) × R) ℂ)
    (hρ : QAlgorithms.IsDensityMatrix ρ) :
    (∫ U, ((Matrix.kroneckerMap (· * ·) (piEqTwo (2 ^ n)) (1 : Matrix R R ℂ) *
        (Matrix.kroneckerMap (· * ·) (Matrix.kroneckerMap (· * ·) (U : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ)
          (U : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ)) (1 : Matrix R R ℂ)) * ρ *
        (Matrix.kroneckerMap (· * ·) (Matrix.kroneckerMap (· * ·) (U : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ)
          (U : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ)) (1 : Matrix R R ℂ))ᴴ).trace.re) ∂(haar n)) =
        2 / (2 ^ n + 1) * (Matrix.kroneckerMap (· * ·) (piSym (2 ^ n)) (1 : Matrix R R ℂ) * ρ).trace.re ∧
    (∫ U, ((Matrix.kroneckerMap (· * ·) (piEqTwo (2 ^ n)) (1 : Matrix R R ℂ) *
        (Matrix.kroneckerMap (· * ·) (Matrix.kroneckerMap (· * ·) (U : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ)
          (U : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ)) (1 : Matrix R R ℂ)) * ρ *
        (Matrix.kroneckerMap (· * ·) (Matrix.kroneckerMap (· * ·) (U : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ)
          (U : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ)) (1 : Matrix R R ℂ))ᴴ).trace.re) ∂(haar n)) ≤ 2 / (2 ^ n + 1) ∧
    ((∫ U, ((Matrix.kroneckerMap (· * ·) (piEqTwo (2 ^ n)) (1 : Matrix R R ℂ) *
        (Matrix.kroneckerMap (· * ·) (Matrix.kroneckerMap (· * ·) (U : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ)
          (U : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ)) (1 : Matrix R R ℂ)) * ρ *
        (Matrix.kroneckerMap (· * ·) (Matrix.kroneckerMap (· * ·) (U : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ)
          (U : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ)) (1 : Matrix R R ℂ))ᴴ).trace.re) ∂(haar n)) = 2 / (2 ^ n + 1) ↔
      Matrix.kroneckerMap (· * ·) (piSym (2 ^ n)) (1 : Matrix R R ℂ) * ρ = ρ) := by sorry

end PRUPermLayer
