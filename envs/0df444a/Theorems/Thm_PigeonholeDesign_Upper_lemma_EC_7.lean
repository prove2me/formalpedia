-- Prove2me | Theorems.Thm_PigeonholeDesign_Upper_lemma_EC_7
-- name    : PigeonholeDesign.Upper.lemma_EC_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T03:12:19.4681+00:00
-- url     : https://prove2.me/theorems/0f0d00c7-b5ff-490b-bb15-0162cef1bd1c
-- title:
--   Lemma EC.7 (corrected) — swapping x_{i+1} and x_{j+1} does not decrease the single-pigeonhole design's expected discrepancy
-- statement:
--   Let $T$ be even and $x=(x_1,\dots,x_T)\in\mathbb R^T$ an arrival instance, and let $x'_1\le\dots\le x'_T$ be its smallest-to-largest rearrangement, given by a fixed sorting permutation; the rank of subject $t$ is its position in that rearrangement. Let $i\ne j$ be odd indices with $i+1,j+1\le T$ such that $x_i,x_{i+1}$ both lie in the lower half $\{x'_1,\dots,x'_{T/2}\}$ (rank at most $T/2$) and $x_j,x_{j+1}$ both lie in the upper half $\{x'_{T/2+1},\dots,x'_T\}$ (rank above $T/2$). Let $\sigma$ be the transposition of $i+1$ and $j+1$. Then the pigeonhole design with a single pigeonhole $\mathcal P(S)=\{S\}$ satisfies
--   $$\mathbb E\bigl[d_{A,B}\ \text{on}\ (x_1,\dots,x_T)\bigr]\ \le\ \mathbb E\bigl[d_{A,B}\ \text{on}\ (x_{\sigma(1)},\dots,x_{\sigma(T)})\bigr].$$
--
--   This exchange step drives the proof of Proposition EC.1: repeatedly swapping moves the instance toward one whose consecutive pairs straddle the median, which maximizes the design's expected discrepancy.
--
--   **Formalization Note** The paper states that some rearrangement incurs a *larger* discrepancy. The strict form is false (if all $x_t$ are equal, every rearrangement gives the same value), and the non-strict form with "some rearrangement" is trivial (take $\sigma$ the identity). The proof (pp. ec11–ec13) establishes the non-strict inequality for the specific transposition $\sigma=(i{+}1\ \ j{+}1)$, which is what is stated; the paper's "there exists $j$" step is made a hypothesis. Indices are 0-based in Lean, so the paper's odd 1-based $i$ is an even 0-based position, and the rank condition "rank $\le T/2$" becomes 0-based rank $<T/2$. With ties among the $x_t$, the halves are those of the fixed sorting permutation `Tuple.sort x`. The single-pigeonhole design is the pigeonhole design with the constant labelling.
-- source:
--   Zhao and Zhou, Pigeonhole Design: Balancing Sequential Experiments from an Online Matching Perspective, arXiv:2201.12936v6, p. ec11 (PDF p. 49), Lemma EC.7 and its proof pp. ec11-ec13 (corrected: specific swap σ = (i+1 j+1), non-strict inequality)

import Mathlib
import Definitions.Def_PigeonholeDesign_Upper_Setting

namespace PigeonholeDesign.Upper

theorem lemma_EC_7 {T : ℕ} (hT : Even T) (x : Fin T → ℝ) (i j : ℕ)
    (hi : Even i) (hj : Even j) (hij : i ≠ j) (hi1 : i + 1 < T) (hj1 : j + 1 < T)
    (hlow : (((Tuple.sort x).symm ⟨i, Nat.lt_of_succ_lt hi1⟩ : Fin T) : ℕ) < T / 2 ∧
      (((Tuple.sort x).symm ⟨i + 1, hi1⟩ : Fin T) : ℕ) < T / 2)
    (hup : T / 2 ≤ (((Tuple.sort x).symm ⟨j, Nat.lt_of_succ_lt hj1⟩ : Fin T) : ℕ) ∧
      T / 2 ≤ (((Tuple.sort x).symm ⟨j + 1, hj1⟩ : Fin T) : ℕ)) :
    phdExp (fun _ : ℝ => ()) x ≤
      phdExp (fun _ : ℝ => ()) (x ∘ Equiv.swap (⟨i + 1, hi1⟩ : Fin T) ⟨j + 1, hj1⟩) := by sorry

end PigeonholeDesign.Upper
