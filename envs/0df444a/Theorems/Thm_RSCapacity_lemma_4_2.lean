-- Prove2me | Theorems.Thm_RSCapacity_lemma_4_2
-- name    : RSCapacity.lemma_4_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T11:29:52.099543+00:00
-- url     : https://prove2.me/theorems/f232ee7b-2cb3-459e-9d37-1b9d3396d395
-- title:
--   Lemma 4.2 (One agreement gives multiplicity $m$)
-- statement:
--   Let $F$ be a field, $r\ge1$, $m\ge0$, $(\alpha,y)\in F^2$, $Q\in F[X,Y_0,\dots,Y_r]$ and $P\in F[X]$. If $P(\alpha)=y$ and $Q$ obeys the local constraints (24) at $(\alpha,y)$, then
--   $$Q\bigl(\alpha+T,P(\alpha+T),P^{[1]}(\alpha+T),\dots,P^{[r]}(\alpha+T)\bigr)\equiv0\pmod{T^m}.$$
--
--   So the decoder, which knows only the value $P(\alpha)$ and not its derivatives, still forces a root of multiplicity $m$ at every agreement.
--
--   Differences from the source:
--   - generalization: Q in the interpolation space 𝒬 under the §4.1 standing hypotheses → any Q ∈ F[X, Y_0, …, Y_r], any r ≥ 1 and m; reason: the proof uses only Equation (13) and the constraints (24); 𝒬 is a special case
--   - encoding: ≡ 0 (mod T^m) → X^m divides the univariate polynomial obtained by X ↦ α + X, Y_j ↦ P^{[j]}(α + X); reason: T is the variable of F[X]
-- source:
--   Jeronimo, Algorithmic List Decoding at Capacity and Optimal Proximity Gaps for Reed–Solomon Codes, arXiv:2609.05870 (held version of November 1, 2026, sha256 9a0069bd…), Lemma 4.2, p.14 (PDF 16)

import Mathlib
import Definitions.Def_RSCapacity_LocalConstraints

open Polynomial

set_option autoImplicit false

namespace RSCapacity

/-- **Lemma 4.2 (One agreement gives multiplicity m).** Jeronimo, arXiv:2609.05870 (held version of November 1, 2026, sha256 9a0069bd…),
Lemma 4.2, p.14 (PDF 16). If P(α) = y and Q obeys Equation (24) at (α, y), then
Q(α + T, P(α + T), P^{[1]}(α + T), …, P^{[r]}(α + T)) ≡ 0 (mod T^m).

**Formalization Note.** Stated for every Q ∈ F[X, Y_0, …, Y_r], not only Q ∈ 𝒬 (the proof uses
nothing about 𝒬). T is the variable of `F[X]`; the left side substitutes X ↦ α + T and
Y_j ↦ P^{[j]}(α + T). -/
theorem lemma_4_2 {F : Type*} [Field F] (r m : ℕ) (hr : 1 ≤ r) (α y : F)
    (Q : MvPolynomial (Fin (r + 2)) F) (P : F[X]) (hPy : P.eval α = y)
    (hQ : ObeysLocal r m α y Q) :
    (X : F[X]) ^ m ∣ MvPolynomial.aeval (Fin.cases (motive := fun _ => F[X]) (C α + X)
      (fun j : Fin (r + 1) => (hasseDeriv (j : ℕ) P).comp (C α + X))) Q := by sorry

end RSCapacity
