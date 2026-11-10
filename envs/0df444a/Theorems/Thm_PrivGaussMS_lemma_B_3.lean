-- Prove2me | Theorems.Thm_PrivGaussMS_lemma_B_3
-- name    : PrivGaussMS.lemma_B_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T04:10:56.055316+00:00
-- url     : https://prove2.me/theorems/aa53e52f-9ae1-46c5-8114-5de7b3fb04f6
-- title:
--   Lemma B.3 — properties of the weights: sensitivity of $g$, survivor guarantees, $\|B^{-1/2}B'B^{-1/2}-I\|_*\le16\lambda/n$, affine invariance, measurability
-- statement:
--   Let $k,\lambda\ge1$ be integers with $n\ge16k\lambda$. For every dataset $x$ of $n$ records of $\mathbb R^d$ and every neighbouring dataset $x'$ (primes denote its outputs):
--
--   1. $0\le g\le k$ and $|g-g'|\le1$.
--   2. If $g<k$, then the recorded set $A=[n]\setminus I_k$ has fewer than $k$ rows, all deleted by the pruning run at threshold $u_k\ge\lambda$ (which does not stop on a singular statistic), and
--   $$\rho_i=1\ (i\notin A),\qquad 0\prec T_{A^c}\preceq B\preceq T,\qquad n-|A|\le b\le n.$$
--   3. If $g,g'<k$, then $\|B^{-1/2}B'B^{-1/2}-I_{d+1}\|_*\le16\lambda/n$.
--   4. Pruning at threshold $\lambda$ returns at most $n-g$ survivors.
--
--   Moreover, for every invertible $F\in\mathbb R^{d\times d}$ and $v\in\mathbb R^d$, replacing each $x_i$ by $Fx_i+v$ leaves every $I_j$, $g$ and every $\rho_i$ unchanged and sends $B$ to $\begin{pmatrix}F&v\\0&1\end{pmatrix}B\begin{pmatrix}F&v\\0&1\end{pmatrix}^T$; and the maps $x\mapsto I_j$, $g$, $\rho$, $B$, $A$ are Borel measurable.
--
--   These stability properties feed the privacy test and the correction.
--
--   Differences from the source:
--   - encoding: 'A consists of fewer than k rows deleted at a threshold at least λ' → |A| < k, the pruning run at u_k did not stop on a singular statistic, its deleted rows are exactly A, and λ ≤ u_k; reason: A = [n] ∖ I_k is by definition the set deleted at u_k
--   - reading: the lemma's parameters → integers k, λ ≥ 1 and n ≥ 16kλ; reason: the standing condition stated with (16), p.37
--   - encoding: 'affine invariant' → for x_i ↦ F x_i + v with det F a unit; reason: the paper's invertible affine maps (pp.36, 39)
--   - encoding: 'All outputs are Borel measurable' → Measurable with the discrete σ-algebra on ℕ and on finite sets, product Borel on vectors and matrices; reason: these outputs take finitely many values or are real vectors
-- source:
--   Moayedi, Yassaee, Ebrahimi, Optimal Private Gaussian Multi-sampling, STOC 2027 submission (manuscript sha256 1838c582…), Lemma B.3, pp.37–38; hypotheses from (16), p.37

import Mathlib
import Definitions.Def_PrivGaussMS_Pruning

open MeasureTheory Matrix PrivateUniformGen.Characterization
open scoped MatrixOrder

namespace PrivGaussMS

/-- **Lemma B.3** (Properties of the weights), Moayedi, Yassaee, Ebrahimi, *Optimal Private
Gaussian Multi-sampling*, STOC 2027 submission (manuscript sha256 1838c582…), pp.37–38.

For integers `k, λ ≥ 1` with `n ≥ 16kλ` (16), the routine (16)–(17) satisfies, primes denoting its
output on a neighbouring dataset:
1. `0 ≤ g ≤ k` and `|g − g'| ≤ 1`;
2. if `g < k`, the recorded set `A` consists of fewer than `k` rows deleted at a threshold at least
   `λ`, and `ρ_i = 1 (i ∉ A)`, `0 ≺ T_{Aᶜ} ⪯ B ⪯ T`, `n − |A| ≤ b ≤ n`;
3. if `g, g' < k`, then `∥B^{−1/2}B′B^{−1/2} − I_{d+1}∥_∗ ≤ 16λ/n`;
4. pruning at threshold `λ` returns at most `n − g` survivors.
The sets `I_j`, the score `g` and the weights `ρ_i` are affine invariant, `B` transforms by the
corresponding augmented congruence, and all outputs are Borel measurable.

**Formalization Note.** "`A` consists of rows deleted at a threshold at least `λ`" is: the pruning
run at `u_k ≥ λ` that defines `I_k` did not stop on a singular statistic and its deleted rows are
exactly `A = [n] \ I_k`. Affine maps are `x_i ↦ F x_i + v` with `F` invertible. The σ-algebras on
`ℕ` and `Finset (Fin n)` are discrete; `⪯` is the Loewner order. -/
theorem lemma_B_3 {n d : ℕ} (k lam : ℕ) (hk : 1 ≤ k) (hlam : 1 ≤ lam) (hn : 16 * k * lam ≤ n) :
    (∀ x : Fin n → Vec d, score x k lam ≤ k) ∧
    (∀ x x' : Fin n → Vec d, Neighbors x x' →
      |(score x k lam : ℤ) - (score x' k lam : ℤ)| ≤ 1) ∧
    (∀ x : Fin n → Vec d, score x k lam < k →
      (recordedSet x k lam).card < k ∧
      ((prune x (uThr n lam k)).aborted = false ∧
        (prune x (uThr n lam k)).deleted.toFinset = recordedSet x k lam ∧
        (lam : ℝ) ≤ uThr n lam k) ∧
      (∀ i, i ∉ recordedSet x k lam → weights x k lam i = 1) ∧
      (statI x (recordedSet x k lam)ᶜ).PosDef ∧
      statI x (recordedSet x k lam)ᶜ ≤ Bstat x k lam ∧ Bstat x k lam ≤ Tstat x ∧
      (n : ℝ) - (recordedSet x k lam).card ≤ bw (Bstat x k lam) ∧
      bw (Bstat x k lam) ≤ n) ∧
    (∀ x x' : Fin n → Vec d, Neighbors x x' → score x k lam < k → score x' k lam < k →
      nuclearNorm (relChange (Bstat x k lam) (Bstat x' k lam)) ≤ 16 * lam / n) ∧
    (∀ x : Fin n → Vec d, (prune x (lam : ℝ)).survivors.card ≤ n - score x k lam) ∧
    (∀ (F : Matrix (Fin d) (Fin d) ℝ) (v : Fin d → ℝ), IsUnit F.det → ∀ x : Fin n → Vec d,
      (∀ j, survivorsAt (affineData F v x) lam j = survivorsAt x lam j) ∧
      score (affineData F v x) k lam = score x k lam ∧
      weights (affineData F v x) k lam = weights x k lam ∧
      Bstat (affineData F v x) k lam = augAffine F v * Bstat x k lam * (augAffine F v)ᵀ) ∧
    (∀ j, Measurable fun x : Fin n → Vec d => survivorsAt x lam j) ∧
    Measurable (fun x : Fin n → Vec d => score x k lam) ∧
    Measurable (fun x : Fin n → Vec d => weights x k lam) ∧
    Measurable (fun x : Fin n → Vec d => Bstat x k lam) ∧
    Measurable (fun x : Fin n → Vec d => recordedSet x k lam) := by sorry

end PrivGaussMS
