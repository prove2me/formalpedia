-- Prove2me | Theorems.Thm_SpencerEight_lemma_8_44
-- name    : SpencerEight.lemma_8_44
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T11:12:44.435341+00:00
-- url     : https://prove2.me/theorems/808be101-5797-45cd-8618-0838399d30d1
-- title:
--   Lemma 8.44 — hereditary spectral slack
-- statement:
--   Let $B_i\in\mathbb R^{n\times n}$ be symmetric contractions with $\operatorname{tr}[B_i^2]\le\rho n$, and let $M$ satisfy $\|M\|\le L\sqrt n$, where $0<L<C$. Put $g:=C-L$ and $U:=|M|/(L\sqrt n)$. Suppose $p(u):=\sum_{j=0}^da_ju^{2j}$ has nonnegative coefficients and
--   $$\frac{(C-L)^2}{(C-Lu)^2}\le p(u)\quad(0\le u\le1),\qquad\operatorname{tr}[p(U)-a_0I]\le n\mu.$$
--   For every remaining coefficient put $H:=C\sqrt nI-|M|$ and $D_i:=g\sqrt nH^{-1/2}B_iH^{-1/2}$. Then $D_i$ is a symmetric contraction and $\operatorname{tr}[D_i^2]\le\rho'n$, where $\rho':=a_0\rho+\mu$. Moreover, if the transformed family has a complete signing of norm at most $F\sqrt n$ with $0\le F\le g$, then the current untransformed family has a complete signing whose sum with $M$ has norm at most $(L+F)\sqrt n$.
--
--   Conjugating the residual family by the remaining headroom lowers its traces, while the costs of the phases still add.
--
--   Differences from the source:
--   - generalization: M a partial signed sum → any symmetric M with ‖M‖ ≤ L√n; reason: the page's proof uses only these two properties; a partial signed sum is such a matrix
--   - encoding: U := |M|/(L√n), n the dimension → 0 < n; reason: a nondegeneracy condition: it excludes only the division by zero
--   - reading: a complete signing of the current family of norm at most (L + F)√n → ‖M + Σ ε_i B_i‖ ≤ (L + F)√n; reason: the proof bounds M + Δ; this is the partial sum so far together with the residual signing
-- source:
--   Song, Zhang, Matrix Spencer: Eight Standard Deviations Suffice and an Almost-Linear Time Algorithm for Dense Input, arXiv:2609.15025 (held version, sha256 9ccbcdb8…), Lemma 8.44, p.105 (PDF p.105)

import Mathlib
import Definitions.Def_SpencerEight_IsSymmContraction
import Definitions.Def_SpencerEight_signedSum
import Definitions.Def_SpencerEight_absM
import Definitions.Def_BlockBochner_invSqrt
import Definitions.Def_SpencerEight_evenPoly
open scoped Matrix.Norms.L2Operator

namespace SpencerEight

/-- Lemma 8.44 (Hereditary spectral slack), Song, Zhang, *Matrix Spencer: Eight Standard Deviations Suffice and an Almost-Linear Time Algorithm for Dense Input*, arXiv:2609.15025 (held version, sha256 9ccbcdb8…), p.105 (PDF p.105).

**Formalization Note** `M` is any symmetric matrix with `‖M‖ ≤ L√n`; the lemma's "partial signed sum" enters the proof only through these two facts. `p(u) = ∑_{j≤d} a_j u^{2j}`. `n > 0` because the page divides by `L√n`. The moreover clause adds `M` to the signed sum of the untransformed family. -/
theorem lemma_8_44 {n : ℕ} (hn : 0 < n) {ι : Type*} [Fintype ι]
    (B : ι → Matrix (Fin n) (Fin n) ℝ) (hB : ∀ i, IsSymmContraction (B i)) {ρ : ℝ}
    (hρ : ∀ i, (B i ^ 2).trace ≤ ρ * n) (M : Matrix (Fin n) (Fin n) ℝ) (hMs : M.IsSymm)
    {L C μ : ℝ} (hL : 0 < L) (hLC : L < C) (hM : ‖M‖ ≤ L * Real.sqrt n)
    (deg : ℕ) (a : ℕ → ℝ) (ha : ∀ j, 0 ≤ a j)
    (hp : ∀ u : ℝ, 0 ≤ u → u ≤ 1 →
      (C - L) ^ 2 / (C - L * u) ^ 2 ≤ ∑ j ∈ Finset.range (deg + 1), a j * u ^ (2 * j))
    (hμ : (evenPoly a deg ((L * Real.sqrt n)⁻¹ • absM M) -
      a 0 • (1 : Matrix (Fin n) (Fin n) ℝ)).trace ≤ n * μ) :
    let D : ι → Matrix (Fin n) (Fin n) ℝ := fun i =>
      ((C - L) * Real.sqrt n) •
        (BlockBochner.invSqrt ((C * Real.sqrt n) • (1 : Matrix (Fin n) (Fin n) ℝ) - absM M) * B i *
          BlockBochner.invSqrt ((C * Real.sqrt n) • (1 : Matrix (Fin n) (Fin n) ℝ) - absM M))
    (∀ i, IsSymmContraction (D i) ∧ (D i ^ 2).trace ≤ (a 0 * ρ + μ) * n) ∧
    (∀ F : ℝ, 0 ≤ F → F ≤ C - L →
      (∃ ε : ι → ℝ, (∀ i, ε i = 1 ∨ ε i = -1) ∧ ‖signedSum D ε‖ ≤ F * Real.sqrt n) →
      ∃ ε : ι → ℝ, (∀ i, ε i = 1 ∨ ε i = -1) ∧
        ‖M + signedSum B ε‖ ≤ (L + F) * Real.sqrt n) := by sorry

end SpencerEight
