-- Prove2me | Theorems.Thm_TarskiBootstrap_Dimensional_theorem_1_1
-- name    : TarskiBootstrap.Dimensional.theorem_1_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T07:29:52.61981+00:00
-- url     : https://prove2.me/theorems/2fa951a2-359f-4cae-8d80-8275796de0f8
-- title:
--   Theorem 1.1 — Dimensional hardness bootstrapping
-- statement:
--   Let $n,k$ be positive integers. Let $F$ be a set of monotone maps $[n]^k\to[n]^k$, each with a unique fixed point $f^*$, and suppose the entire answer set $A=\{f^*:f\in F\}$ is an antichain. Let $\lambda\in\mathbb R$, $\delta>0$, and suppose there exists a nonnegative symmetric adversary $\Gamma_0$ on $F$, zero between equal fixed-point answers, with
--
--   $$\|\Gamma_0\|_{2\to2}\ge\lambda,\qquad\forall x\in[n]^k,\quad\|\Gamma_0\circ\Delta_x\|_{2\to2}\le\delta.$$
--
--   For every positive integer $t$, take exactly the prescribed family $F'=C_t(F^t)$. Every member of $F'$ is monotone and has a unique fixed point, and its entire set of possible fixed points is an antichain. There exists a nonnegative symmetric adversary $\Gamma'$ on the actual maps of $F'$, zero between equal fixed-point answers, with
--
--   $$\|\Gamma'\|_{2\to2}\ge t\lambda,\qquad\forall\mathbf x\in[n]^{tk},\quad\|\Gamma'\circ\Delta_{\mathbf x}\|_{2\to2}\le(5+2\sqrt2)\delta.$$
--
--   Both inequalities retain the source witness scale. Empty families, singleton families, shared answers, zero matrices and nonpositive $\lambda$ remain within the statement. The theorem is the paper's dimensional transformation at unchanged width.
--
--   Differences from the source:
--   - encoding: positive integers n, k and t and the grid [n]^(tk) → PNat parameters, Fin coordinates, and the block grid with the explicit flattenBlocks order equivalence; reason: the coordinate bijection preserves the full grid and its coordinatewise order
--   - encoding: the unique fixed point f* → a total choice selector used only under the unique-fixed-point assumptions; reason: on these instances the chosen answer is forced; the no-fixed-point fallback is never used
--   - encoding: spectral matrix norm → operator norm of Matrix.toEuclideanCLM over real Euclidean space; reason: this is exactly the unnormalized real l2-to-l2 norm and removes matrix norm instance ambiguity
--   - encoding: there exists Fprime equal to C_t(F^t), with its listed properties → the conclusions are asserted directly for the defined chainFamily; reason: substitution of the prescribed family for an existential variable with a forced value changes no instances
--   - reading: a family of hard instances for Tarski(n, k), a term the source does not define separately → a set of monotone endomaps of the grid, with no further condition; reason: hardness enters only through the adversary witness; this is the broadest reading, so every source instance is covered
--   - encoding: one-based blocks 1,...,t and the sentinel sigma = t+1 → zero-based Fin t blocks and the sentinel t in firstNonfixed; reason: a uniform shift by one; the guard in chain never reads the sentinel as a block
--   - encoding: max over query indices i of the norm of Gamma o Delta_i is at most delta, equation (2.9) → the same bound for every query x in SpectralWitness; reason: the query set is a finite nonempty grid, so the two conditions are equivalent
-- source:
--   Li, Ma, Yang and Zhao, Bootstrapping Classical and Quantum Query Lower Bounds for Finding Tarski Fixed Points, STOC 2027 submission #6 (2026), frozen preprint, Theorem 1.1, PDF/printed p. 4, repeated p. 10; proof p. 15; Definition 3.1 p. 11; equation (2.9) p. 7, SHA-256 320afa8333f95589a388b30ffbfd6d7b7e5d93cdf07fa8630825fbf7d0107d59; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/6.pdf. No arXiv identifier/version supplied.

import Definitions.Def_TarskiBootstrap_Dimensional_ChainFamily
import Definitions.Def_TarskiBootstrap_Dimensional_Witness

open scoped Matrix

namespace TarskiBootstrap.Dimensional

open scoped Classical

/-- Full Theorem 1.1, PDF/printed pp. 4, 10; proof p. 15. -/
theorem theorem_1_1 {n k : ℕ+}
    (F : Set (Grid n k → Grid n k))
    (hF : ∀ f : F, Monotone f.val ∧ ∃! x, f.val x = x)
    (hA : IsAntichain (· ≤ ·) (possibleAnswers F))
    (lam δ : ℝ) (hδ : 0 < δ)
    (hwitness : ∃ Γ₀ : Matrix F F ℝ,
      NonnegativeAdversary (fun f : F => fixedPoint f.val) Γ₀ ∧
      SpectralWitness (fun f : F => f.val) Γ₀ lam δ) (t : ℕ+) :
    (∀ g : chainFamily t (possibleAnswers F) F,
      Monotone g.val ∧ ∃! x, g.val x = x) ∧
    IsAntichain (· ≤ ·) (possibleAnswers (chainFamily t (possibleAnswers F) F)) ∧
    ∃ Γ' : Matrix (chainFamily t (possibleAnswers F) F)
                   (chainFamily t (possibleAnswers F) F) ℝ,
      NonnegativeAdversary
        (fun g : chainFamily t (possibleAnswers F) F => fixedPoint g.val) Γ' ∧
      SpectralWitness
        (fun g : chainFamily t (possibleAnswers F) F => g.val)
        Γ' ((t : ℝ) * lam) ((5 + 2 * Real.sqrt 2) * δ) := by sorry

end TarskiBootstrap.Dimensional
