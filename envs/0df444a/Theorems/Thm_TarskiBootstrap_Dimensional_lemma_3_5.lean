-- Prove2me | Theorems.Thm_TarskiBootstrap_Dimensional_lemma_3_5
-- name    : TarskiBootstrap.Dimensional.lemma_3_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T07:35:23.25823+00:00
-- url     : https://prove2.me/theorems/3d5a2567-1ca7-45aa-b107-95ece7e79ffd
-- title:
--   Lemma 3.5 — Numerator lower bound
-- statement:
--   Let $F,\Gamma_0,\lambda,\delta,v$ and the positive integers $n,k,t$ have the full Section 3.2 meaning: $F$ consists of monotone grid maps with unique fixed points forming an antichain, $\Gamma_0$ is a nonnegative adversary with spectral witness $(\lambda,\delta)$, $\delta>0$, and $v$ is a nonnegative unit Perron vector for $\Gamma_0$. For the specific tensor sum $\Gamma$ in (3.7),
--
--   $$\|\Gamma\|_{2\to2}\ge t\lambda.$$
--
--   This is the numerator inequality for dimensional amplification; it does not assume that inequality for a new matrix.
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
-- source:
--   Li, Ma, Yang and Zhao, Bootstrapping Classical and Quantum Query Lower Bounds for Finding Tarski Fixed Points, STOC 2027 submission #6 (2026), frozen preprint, Lemma 3.5, equations (3.9)–(3.10), with common §3.2 context, PDF/printed p. 13, SHA-256 320afa8333f95589a388b30ffbfd6d7b7e5d93cdf07fa8630825fbf7d0107d59; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/6.pdf. No arXiv identifier/version supplied.

import Definitions.Def_TarskiBootstrap_Dimensional_ImageAdversary

open scoped Matrix

namespace TarskiBootstrap.Dimensional

open scoped Classical

/-- Lemma 3.5, PDF/printed p. 13, with the common Section 3.2 context. -/
theorem lemma_3_5 {n k : ℕ+} (t : ℕ+) (F : Set (Grid n k → Grid n k))
    (hF : ∀ f : F, Monotone f.val ∧ ∃! x, f.val x = x)
    (hA : IsAntichain (· ≤ ·) (possibleAnswers F))
    (Γ₀ : Matrix F F ℝ) (lam δ : ℝ) (hδ : 0 < δ)
    (hΓ₀ : NonnegativeAdversary (fun f : F => fixedPoint f.val) Γ₀)
    (hw : SpectralWitness (fun f : F => f.val) Γ₀ lam δ)
    (v : EuclideanSpace ℝ F) (hvnonneg : ∀ f, 0 ≤ v f) (hvunit : ‖v‖ = 1)
    (hveigen : Matrix.toEuclideanCLM (𝕜 := ℝ) Γ₀ v = ‖Matrix.toEuclideanCLM (𝕜 := ℝ) Γ₀‖ • v) :
    (t : ℝ) * lam ≤ ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (tensorAdversary t Γ₀ v)‖ := by sorry

end TarskiBootstrap.Dimensional
