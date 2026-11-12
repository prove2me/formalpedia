-- Prove2me | Theorems.Thm_QSampVerif_lemma_3_19
-- name    : QSampVerif.lemma_3_19
-- status  : Open
-- author  : @iris
-- created : 2026-11-11T08:27:31.531204+00:00
-- url     : https://prove2.me/theorems/881d2782-ba77-44c4-bb9e-72b86decc662
-- title:
--   Lemma 3.19 — Pauli character cancellation
-- statement:
--   For an arbitrary operator $\rho$ on $\mathbb C^2\otimes\mathcal K$ (possibly rectangular, $\mathbb C^2\otimes\mathcal K'\to\mathbb C^2\otimes\mathcal K$) and operators $B_{a,b}$, $C_{a,b}$ of compatible dimensions,
--
--   $$\frac14\sum_{r,x\in\mathbb F_2}\ \sum_{a,b,a',b'\in\mathbb F_2}(-1)^{r(a+a')+x(b+b')}\,(X^aZ^b\otimes B_{a,b})\,\rho\,(X^{a'}Z^{b'}\otimes C_{a',b'})^\dagger=\sum_{a,b\in\mathbb F_2}(X^aZ^b\otimes B_{a,b})\,\rho\,(X^aZ^b\otimes C_{a,b})^\dagger .$$
--
--   The identity is the character cancellation of partial Pauli twirling; it holds for non-positive cross operators as well.
--
--   Differences from the source:
--   - encoding: F₂; X^aZ^b; operators of compatible dimensions → ZMod 2 with exponents a.val; the published pauliX, pauliZ; ρ : (Bool × κ') → (Bool × κ), B_{a,b} : κ → κ₁, C_{a,b} : κ' → κ₂ (qubit first); reason: same objects
-- source:
--   Chung, Cojocaru, Lee, Lin, Classical Verification of Quantum Sampling with Negligible Error, STOC 2027 submission (held version, sha256 dbc19d8f…7ee7), Lemma 3.19, p.23 (PDF 24)

import Definitions.Def_QAlgorithms_Defs_Gates

set_option autoImplicit false

namespace QSampVerif

open QAlgorithms
open scoped Matrix Kronecker

/-- Chung, Cojocaru, Lee, Lin, STOC 2027 submission (held version, sha256 dbc19d8f…7ee7),
Lemma 3.19 (Pauli character cancellation), p.23 (PDF 24).

For an arbitrary operator `ρ` and operators `B_{a,b}`, `C_{a,b}` of compatible dimensions,
`(1/4) Σ_{r,x ∈ F₂} Σ_{a,b,a',b' ∈ F₂} (−1)^{r(a+a') + x(b+b')} (X^a Z^b ⊗ B_{a,b}) ρ
(X^{a'} Z^{b'} ⊗ C_{a',b'})† = Σ_{a,b ∈ F₂} (X^a Z^b ⊗ B_{a,b}) ρ (X^a Z^b ⊗ C_{a,b})†`.

**Formalization Note.** `F₂ = ZMod 2`; `X, Z` are the published `pauliX`, `pauliZ`; the qubit is
the first tensor factor; `ρ` and the `B`, `C` may be rectangular. -/
theorem lemma_3_19 {κ κ' κ₁ κ₂ : Type*} [Fintype κ] [Fintype κ'] [Fintype κ₁] [Fintype κ₂]
    (ρ : Matrix (Bool × κ) (Bool × κ') ℂ) (B : ZMod 2 → ZMod 2 → Matrix κ₁ κ ℂ)
    (C : ZMod 2 → ZMod 2 → Matrix κ₂ κ' ℂ) :
    (1 / 4 : ℂ) • ∑ r : ZMod 2, ∑ x : ZMod 2, ∑ a : ZMod 2, ∑ b : ZMod 2, ∑ a' : ZMod 2,
      ∑ b' : ZMod 2, ((-1 : ℂ) ^ (r * (a + a') + x * (b + b')).val) •
        (((pauliX ^ a.val * pauliZ ^ b.val) ⊗ₖ B a b) * ρ *
          ((pauliX ^ a'.val * pauliZ ^ b'.val) ⊗ₖ C a' b')ᴴ) =
    ∑ a : ZMod 2, ∑ b : ZMod 2,
      ((pauliX ^ a.val * pauliZ ^ b.val) ⊗ₖ B a b) * ρ *
        ((pauliX ^ a.val * pauliZ ^ b.val) ⊗ₖ C a b)ᴴ := by sorry

end QSampVerif
