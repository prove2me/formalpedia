-- Prove2me | Theorems.Thm_SymThrWires_Main_lemma_6_1
-- name    : SymThrWires.Main.lemma_6_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T00:17:05.468063+00:00
-- url     : https://prove2.me/theorems/4c8b9ed1-e860-4642-9cd4-f51c1d8acfe5
-- title:
--   Lemma 6.1 — integer threshold masks: 1[X ≤ τ] = Σ_{a≤D} c_a (X choose a), |c_a| ≤ 2^a, and the multilinear polynomial P_{τ,D}
-- statement:
--   For nonnegative integers $\tau,D$ let $c_a=\sum_{i=0}^{\min(a,\tau)}(-1)^{a-i}\binom ai$. Then $|c_a|\le2^a$ for $0\le a\le D$, and for every integer $0\le X\le D$
--   $$1[X\le\tau]=\sum_{a=0}^D c_a\binom Xa .$$
--   Equivalently, for Boolean variables $y_1,\dots,y_G$, $P_{\tau,D}(y)=\sum_{a=0}^D c_a e_a(y)$ is a multilinear integer polynomial of degree at most $D$, each coefficient has magnitude at most $2^D$, and $P_{\tau,D}(y)=1[\sum_iy_i\le\tau]$ whenever $\sum_iy_i\le D$. The same identities hold modulo every integer. Writing $X=\sum_iy_i$, if $s\in\{0,1\}$ then $sP_{\tau,D}(y)=s\,1[X\le\tau]$ whenever $X\le D$ or $s=0$.
--
--   The mask that discards high-population points is thus an exact integer polynomial, so the same mask can be used in every residue computation of the counting algorithm.
--
--   **Formalization Note.** Multilinear is stated as: every monomial in the support has every exponent at most $1$. "Modulo every integer" is `Int.ModEq q` for every `q : ℤ`, for both the scalar and the Boolean identity.
--
--   Differences from the source:
--   - encoding: Boolean y_1, …, y_G; s ∈ {0,1} → y : Fin G → Bool evaluated as 0/1 integers; s : ℤ with s = 0 ∨ s = 1; reason: same instances
-- source:
--   Dev Nag, Near-Cubic Gate and Near-Quartic Wire Lower Bounds for SYM∘THR Circuits, STOC 2027 submission, Zenodo doi:10.5281/zenodo.23847026 (sha256 02f54f02…), p. 19, Lemma 6.1

import Mathlib
import Definitions.Def_SymThrWires_Main_Masks

namespace SymThrWires.Main

/-- **Lemma 6.1** (Integer threshold masks, p. 19). For nonnegative integers `τ, D` and
`c_a = Σ_{i=0}^{min(a,τ)} (−1)^{a−i} (a choose i)`: `|c_a| ≤ 2^a` (`0 ≤ a ≤ D`); for every integer
`0 ≤ X ≤ D`, `1[X ≤ τ] = Σ_{a=0}^{D} c_a (X choose a)`; for Boolean `y_1, …, y_G`,
`P_{τ,D} = Σ_{a=0}^{D} c_a e_a` is a multilinear integer polynomial of degree at most `D` with
coefficients of magnitude at most `2^D`, and `P_{τ,D}(y) = 1[Σ y_i ≤ τ]` whenever `Σ y_i ≤ D`; the
same identities hold modulo every integer; and for `s ∈ {0, 1}`, `s P_{τ,D}(y) = s 1[X ≤ τ]`
whenever `X = Σ y_i ≤ D` or `s = 0`. -/
theorem lemma_6_1 (τ D : ℕ) :
    (∀ a, a ≤ D → |newtonCoeff τ a| ≤ 2 ^ a) ∧
    (∀ X : ℕ, X ≤ D →
      (if X ≤ τ then (1 : ℤ) else 0) =
        ∑ a ∈ Finset.range (D + 1), newtonCoeff τ a * (X.choose a : ℤ)) ∧
    (∀ G : ℕ,
      (thresholdPoly τ D G).totalDegree ≤ D ∧
      (∀ s ∈ (thresholdPoly τ D G).support, ∀ i, s i ≤ 1) ∧
      (∀ s, |MvPolynomial.coeff s (thresholdPoly τ D G)| ≤ 2 ^ D) ∧
      ∀ y : Fin G → Bool, (∑ i, (y i).toNat) ≤ D →
        MvPolynomial.eval (fun i => if y i then (1 : ℤ) else 0) (thresholdPoly τ D G) =
          if (∑ i, (y i).toNat) ≤ τ then 1 else 0) ∧
    (∀ q : ℤ,
      (∀ X : ℕ, X ≤ D →
        ∑ a ∈ Finset.range (D + 1), newtonCoeff τ a * (X.choose a : ℤ) ≡
          (if X ≤ τ then 1 else 0) [ZMOD q]) ∧
      ∀ (G : ℕ) (y : Fin G → Bool), (∑ i, (y i).toNat) ≤ D →
        MvPolynomial.eval (fun i => if y i then (1 : ℤ) else 0) (thresholdPoly τ D G) ≡
          (if (∑ i, (y i).toNat) ≤ τ then 1 else 0) [ZMOD q]) ∧
    (∀ (G : ℕ) (y : Fin G → Bool) (s : ℤ), (s = 0 ∨ s = 1) →
      ((∑ i, (y i).toNat) ≤ D ∨ s = 0) →
        s * MvPolynomial.eval (fun i => if y i then (1 : ℤ) else 0) (thresholdPoly τ D G) =
          s * (if (∑ i, (y i).toNat) ≤ τ then 1 else 0)) := by sorry

end SymThrWires.Main
