-- Prove2me | Theorems.Thm_TarskiBootstrap_Dimensional_lemma_3_4
-- name    : TarskiBootstrap.Dimensional.lemma_3_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T07:35:42.643552+00:00
-- url     : https://prove2.me/theorems/785b247f-4ef9-45ac-80cb-a58ac9a3a0c6
-- title:
--   Lemma 3.4 — Validity of the tensor-sum adversary
-- statement:
--   Use the Section 3.2 data: positive $n,k,t$; a family $F$ of monotone grid maps with unique fixed points forming an antichain; a nonnegative adversary $\Gamma_0$ with witness parameters $\lambda\in\mathbb R$, $\delta>0$; and a nonnegative real unit vector $v$ with $\Gamma_0v=\|\Gamma_0\|v$. Form $J=vv^\top$, the ordered tensor terms and their sum $\Gamma$ as in (3.5)–(3.7). Then
--
--   $$\forall\mathbf f,\mathbf g\in F^t,\quad\Gamma[\mathbf f,\mathbf g]=\Gamma[\mathbf g,\mathbf f]\ge0,$$
--   $$ (f_1^*,\ldots,f_t^*)=(g_1^*,\ldots,g_t^*)\implies\Gamma[\mathbf f,\mathbf g]=0.$$
--
--   The same entries transferred to $C_t(F^t)$ form a nonnegative adversary matrix for the chained fixed-point problem. This identifies the constructed matrix as a valid witness candidate.
--
--   Differences from the source:
--   - encoding: positive integers n, k and t and the grid [n]^(tk) → PNat parameters, Fin coordinates, and the block grid with the explicit flattenBlocks order equivalence; reason: the coordinate bijection preserves the full grid and its coordinatewise order
--   - encoding: the unique fixed point f* → a total choice selector used only under the unique-fixed-point assumptions; reason: on these instances the chosen answer is forced; the no-fixed-point fallback is never used
--   - encoding: spectral matrix norm → operator norm of Matrix.toEuclideanCLM over real Euclidean space; reason: this is exactly the unnormalized real l2-to-l2 norm and removes matrix norm instance ambiguity
--   - encoding: the matrix and family data fixed at the start of Section 3.2 → explicit binders for the original family, witness and nonnegative unit Perron vector; reason: the short printed lemma relies on this standing context; no conclusion is made an assumption
--   - encoding: Gamma indexed by C_t(F^t), identified with tuples by Lemma 3.3 → tensorAdversary on tuples, with imageAdversary for the actual image family; reason: injectivity is a separate lemma and gives a bijective permutation of the matrix indices
--   - reading: a family of hard instances for Tarski(n, k), a term the source does not define separately → a set of monotone endomaps of the grid, with no further condition; reason: hardness enters only through the adversary witness; this is the broadest reading, so every source instance is covered
--   - encoding: one-based blocks 1,...,t and the sentinel sigma = t+1 → zero-based Fin t blocks and the sentinel t in firstNonfixed; reason: a uniform shift by one; the guard in chain never reads the sentinel as a block
--   - encoding: max over query indices i of the norm of Gamma o Delta_i is at most delta, equation (2.9) → the same bound for every query x in SpectralWitness; reason: the query set is a finite nonempty grid, so the two conditions are equivalent
--   - encoding: f^(1)* = f^(2)*, the fixed points of the two chained functions → equality of the tuples of component fixed points in clause 2; reason: Lemma 3.3(3) identifies the fixed point of C_t(f) with that tuple, and the printed proof reads it the same way; the image-family clause uses the fixed point of the chained map itself
-- source:
--   Li, Ma, Yang and Zhao, Bootstrapping Classical and Quantum Query Lower Bounds for Finding Tarski Fixed Points, STOC 2027 submission #6 (2026), frozen preprint, Lemma 3.4 and common §3.2 context, PDF/printed p. 13, SHA-256 320afa8333f95589a388b30ffbfd6d7b7e5d93cdf07fa8630825fbf7d0107d59; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/6.pdf. No arXiv identifier/version supplied.

import Definitions.Def_TarskiBootstrap_Dimensional_ImageAdversary

open scoped Matrix

namespace TarskiBootstrap.Dimensional

open scoped Classical

/-- Lemma 3.4, PDF/printed p. 13, with the common Section 3.2 context. -/
theorem lemma_3_4 {n k : ℕ+} (t : ℕ+) (F : Set (Grid n k → Grid n k))
    (hF : ∀ f : F, Monotone f.val ∧ ∃! x, f.val x = x)
    (hA : IsAntichain (· ≤ ·) (possibleAnswers F))
    (Γ₀ : Matrix F F ℝ) (lam δ : ℝ) (hδ : 0 < δ)
    (hΓ₀ : NonnegativeAdversary (fun f : F => fixedPoint f.val) Γ₀)
    (hw : SpectralWitness (fun f : F => f.val) Γ₀ lam δ)
    (v : EuclideanSpace ℝ F) (hvnonneg : ∀ f, 0 ≤ v f) (hvunit : ‖v‖ = 1)
    (hveigen : Matrix.toEuclideanCLM (𝕜 := ℝ) Γ₀ v = ‖Matrix.toEuclideanCLM (𝕜 := ℝ) Γ₀‖ • v) :
    (∀ f g : Fin (t : ℕ) → F,
      tensorAdversary t Γ₀ v f g = tensorAdversary t Γ₀ v g f ∧
      0 ≤ tensorAdversary t Γ₀ v f g) ∧
    (∀ f g : Fin (t : ℕ) → F,
      (fun i => fixedPoint (f i).val) = (fun i => fixedPoint (g i).val) →
      tensorAdversary t Γ₀ v f g = 0) ∧
    NonnegativeAdversary
      (fun g : chainFamily t (possibleAnswers F) F => fixedPoint g.val)
      (imageAdversary t (possibleAnswers F) F Γ₀ v) := by sorry

end TarskiBootstrap.Dimensional
