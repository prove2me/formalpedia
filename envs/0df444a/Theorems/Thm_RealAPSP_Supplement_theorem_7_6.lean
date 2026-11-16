-- Prove2me | Theorems.Thm_RealAPSP_Supplement_theorem_7_6
-- name    : RealAPSP.Supplement.theorem_7_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T04:04:46.418991+00:00
-- url     : https://prove2.me/theorems/39686db5-89c2-4c84-8112-a6e505fb16de
-- title:
--   Theorem 7.6 — BSG covering for approximate reals
-- statement:
--   This is a covering version of the Balog–Szemerédi–Gowers theorem for approximate reals.
--
--   For a finite set $A\subseteq\mathbb R$ and $\Delta\ge0$, write $|A|_{\pm\Delta}$ for the size of a smallest $\Delta$-cover of $A$, i.e. a set $C$ with every $a\in A$ within distance $\Delta$ of some $c\in C$. Write $x=z\pm\Delta$ for $|x-z|\le\Delta$.
--
--   Fix a spacing constant $c_0\ge1$. There is a constant $C$, depending only on $c_0$, with the following two properties.
--
--   1. **Existence.** Let $\Delta\ge0$, let $X,Y\subseteq\mathbb R$ be $\Delta/c_0$-spaced sets of size $n$ each, let $Z\subseteq\mathbb R$ have size at most $n$, and let $L\ge1$ be an integer. Then there are subsets $X_1,\dots,X_L\subseteq X$ and $Y_1,\dots,Y_L\subseteq Y$ such that
--      $$|X_\ell+Y_\ell|_{\pm\Delta}\le C\,L^5n\quad\text{for all }\ell,\qquad |R|\le C\,\frac{n^2}{L},$$
--      where
--      $$R=\{(x,y)\in X\times Y:\ \exists z\in Z:\ x+y=z\pm\Delta\}\setminus\bigcup_{\ell=1}^{L}(X_\ell\times Y_\ell).$$
--   2. **Algorithm.** For every failure exponent $e$ there are a randomized comparison-addition program and a constant $\kappa$ such that, for every $n\ge1$ and every input of this kind ($X$, $Y$, $Z$ given as lists, with $\Delta$ and $L$), the program halts within $\kappa\,n^2(\log(n+2))^{\kappa}$ steps on every sequence of coin flips. With probability at least $1-n^{-e}$ it outputs sets $X_\ell\subseteq X$, $Y_\ell\subseteq Y$ satisfying both bounds of item 1 with the same $C$, together with the set $R$ of these sets, exactly.
--
--   In the paper this is the tool that turns approximately uniform, regular instances into instances with small approximate doubling (§7.4), on the way to the real-to-integer reduction for APSP.
--
--   **Formalization Note** The page's "$\Omega(\Delta)$-spaced" is read as in the proof of Lemma 7.12 (p.39): a constant $c_0\ge1$ is fixed with $X,Y$ being $\Delta/c_0$-spaced, and the $O(\cdot)$ constants depend on it. The output layout is fixed in the supplement's definition `RealAPSP.Supplement.BSG`; the word bound is $(n+L+2)^{c}$.
--
--   Differences from the source:
--   - reading: the comparison-addition model of §1.2, p.3, which also names a "realistic" variant → the published machine RealAPSP.Machine: unit cost, word bound width^c, fair coins preloaded in memory; reason: as in the published Theorem 1.1: the realistic variant defers to [FPS26, Section 1.1], which is not held, and the theorem does not name it
--   - reading: Ω(∆)-spaced, O(L⁵n), O(n²/L) → for every c₀ ≥ 1 a constant C (depending on c₀ only) with X, Y ∆/c₀-spaced and both bounds C·L⁵·n and C·n²/L; reason: the proof of Lemma 7.12 (p.39) fixes "a constant c₀ ≥ 1 such that X and Y are ∆/c₀-spaced", and the O-constants depend on it
--   - reading: the sets … can be computed in randomized time Õ(n²) → for every failure exponent e a program running within κ·n²·(log(n+2))^κ on every coin tape whose output, with probability ≥ 1 − n^{−e}, satisfies both bounds with the same C and lists R exactly; reason: randomized algorithms in the paper are correct with high probability (p.9), read as for the published Theorem 4.7; the stronger reading (the same C for the output) is chosen
--   - encoding: L ≥ 1 and ℓ ∈ [L] → L : ℕ with 1 ≤ L, ℓ : Fin L (0-based); reason: L indexes L subsets, so it is a positive integer
--   - encoding: sets X, Y, Z ⊆ ℝ given to the algorithm, and its output sets → injective lists x, y : Fin n → ℝ, z : Fin m → ℝ with m ≤ n, integer cells n, m, L, real cells ∆, x, y, z; output membership bits and index pairs in the layout of RealAPSP.Supplement.BSG; word bound (n+L+2)^c; reason: the machine reads and writes lists; injectivity makes the lists sets of the stated sizes; the layout lets a large L cost nothing
--   - encoding: the algorithm for all n → for n ≥ 1; reason: at n = 0 the bound κ·n²·… is 0 and no program halts in 0 steps; the instance is empty and the existence clause covers it
-- source:
--   Fischer, Polak, Schmidt, Real-to-Integer Reduction for All-Pairs Shortest Paths, arXiv:2611.04847 (held file sha256 a3dc0096…), Theorem 7.6, p.34 (PDF p.36); restated and proved in §7.6, p.39 (PDF p.41); c₀ from the proof of Lemma 7.12, p.39

import Mathlib
import Definitions.Def_RealAPSP_Supplement_BSG

open Pointwise

namespace RealAPSP

namespace Supplement

/-- **Theorem 7.6 (BSG Covering for Approximate Reals).** Fischer, Polak, Schmidt, *Real-to-Integer Reduction for All-Pairs Shortest Paths*, arXiv:2611.04847 (held file sha256 a3dc0096…), p.34 (PDF p.36); restated and proved in §7.6, p.39 (PDF p.41).

For every spacing constant `c₀ ≥ 1` there is `C` such that two clauses hold. (1) For every `∆ ≥ 0`, all `∆/c₀`-spaced `X, Y ⊆ ℝ` of size `n`, every `Z ⊆ ℝ`
of size at most `n` and every integer `L ≥ 1` there are `X_ℓ ⊆ X`, `Y_ℓ ⊆ Y` (`ℓ < L`) with `|X_ℓ + Y_ℓ|_{±∆} ≤ C·L⁵·n` for all `ℓ` and `|R| ≤ C·n²/L`.
(2) For every failure exponent `e` one program computes such sets and the set `R` exactly, in time `O(n² (log(n+2))^κ)` on every coin tape, correct with
probability at least `1 − n^{−e}`.

**Formalization Note.**
* "Ω(∆)-spaced" is read as in the proof of Lemma 7.12, p.39: "Fix a constant c₀ ≥ 1 such that X and Y are ∆/c₀-spaced". The constant `C` of both
  `O(·)` bounds depends on `c₀` alone, and the same `C` bounds the sets the algorithm outputs.
* "Randomized time Õ(n²)" is read as worst-case time `κ·n²·(log(n+2))^κ` and correctness with high probability, as for the published
  `RealAPSP.theorem_4_7`; `κ` may depend on `e`. The algorithm is stated for `n ≥ 1`.
* Inputs: integer cells `n, m, L`; real cells `∆`, then `x`, `y`, `z`. The word bound is `(n + L + 2)^c`. The output layout is that of
  `bsgOutX`, `bsgOutY` and `bsgOutR` in the definitions module `RealAPSP.Supplement.BSG`. -/
theorem theorem_7_6 :
    ∀ c₀ : ℝ, 1 ≤ c₀ → ∃ C : ℝ,
      (∀ (n L : ℕ), 1 ≤ L → ∀ Δ : ℝ, 0 ≤ Δ → ∀ X Y Z : Finset ℝ,
        X.card = n → Y.card = n → Z.card ≤ n → IsSpaced (Δ / c₀) X → IsSpaced (Δ / c₀) Y →
        ∃ Xs Ys : Fin L → Finset ℝ, (∀ ℓ, Xs ℓ ⊆ X ∧ Ys ℓ ⊆ Y) ∧
          (∀ ℓ, (coverNumber Δ (Xs ℓ + Ys ℓ) : ℝ) ≤ C * (L : ℝ) ^ 5 * n) ∧
          ((bsgRemainder Δ X Y Z Xs Ys).card : ℝ) ≤ C * (n : ℝ) ^ 2 / L) ∧
      ∀ e : ℕ, ∃ (P : Program) (κ : ℝ), ∀ (n m L : ℕ), 1 ≤ n → m ≤ n → 1 ≤ L → ∀ Δ : ℝ, 0 ≤ Δ →
        ∀ (x y : Fin n → ℝ) (z : Fin m → ℝ), Function.Injective x → Function.Injective y → Function.Injective z →
        IsSpaced (Δ / c₀) (valueSet x) → IsSpaced (Δ / c₀) (valueSet y) →
        RunsWhp P (n + L + 2) [(n : ℤ), (m : ℤ), (L : ℤ)] (Δ :: (List.ofFn x ++ List.ofFn y ++ List.ofFn z))
          (κ * (n : ℝ) ^ 2 * Real.log ((n : ℝ) + 2) ^ κ) ((n : ℝ) ^ (-(e : ℝ))) (fun σ =>
            (∀ ℓ, bsgOutX x L σ ℓ ⊆ valueSet x ∧ bsgOutY y L σ ℓ ⊆ valueSet y) ∧
            (∀ ℓ, (coverNumber Δ (bsgOutX x L σ ℓ + bsgOutY y L σ ℓ) : ℝ) ≤ C * (L : ℝ) ^ 5 * n) ∧
            bsgOutR x y σ = bsgRemainder Δ (valueSet x) (valueSet y) (valueSet z) (bsgOutX x L σ) (bsgOutY y L σ) ∧
            ((bsgOutR x y σ).card : ℝ) ≤ C * (n : ℝ) ^ 2 / L) := by sorry

end Supplement

end RealAPSP
