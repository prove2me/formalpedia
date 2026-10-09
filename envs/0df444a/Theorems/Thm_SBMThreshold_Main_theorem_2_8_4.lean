-- Prove2me | Theorems.Thm_SBMThreshold_Main_theorem_2_8_4
-- name    : SBMThreshold.Main.theorem_2_8_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T08:17:27.065362+00:00
-- url     : https://prove2.me/theorems/62dbdf25-7c8a-403c-bf42-4d91a817d6b6
-- title:
--   Theorem 2.8 (4), p. 5 — P[|N^(k)_{u,v} − Y_{u,v}| ≥ |s|^k n^{−4/3} | σ_U] ≤ n^{−1/3+o(1)}
-- statement:
--   Under the hypotheses of Theorem 2.8, let $N^{(k)}_{u,v}$ be the sum of $X_\gamma$ over the non-backtracking paths of length $k=\lceil\alpha\log n\rceil$ from $u$ to $v$. For every sequence $e_n\to0$ there is a sequence $c_n\to0$ such that, for all $n$, all distinct $u,v$, all $U\ni u,v$ with $|U|\le n^{e_n}$ and all labellings $\tau$,
--   $$
--   \mathbb P\bigl[\,|N^{(k)}_{u,v}-Y_{u,v}|\ge|s|^k n^{-4/3}\bigm|\sigma_U=\tau_U\bigr]\le n^{-1/3+c_n}.
--   $$
--
--   The non-backtracking sum $N^{(k)}_{u,v}$, which the algorithm can compute by matrix powering, is with high probability within $|s|^kn^{-4/3}$ of the self-avoiding sum, whose moments displays (1)–(3) control.
--
--   **Formalization Note** The page prints $s^kn^{-4/3}$. Since $s$ may be negative (§3.3.1), for $s<0$ and odd $k$ the printed event would hold always and the claim would be false; the threshold is the magnitude $|s|^k n^{-4/3}$. Assumption 2.7, including the sequence $\ell_n$, is a hypothesis although the display does not mention $\ell$: it is standing for the rest of the article and enters through the proof. The uniformity convention is that of Theorem 2.8 (1).
-- source:
--   Mossel, Neeman and Sly, A Proof of the Block Model Threshold Conjecture, arXiv:1311.4115v4, p. 5, Theorem 2.8, display (4) (s^k read as |s|^k)

import Mathlib
import Definitions.Def_SBMThreshold_Main_Setting
import Definitions.Def_SBMThreshold_Main_Paths
open Filter Topology Finset

namespace SBMThreshold.Main

/-- Theorem 2.8 (4) (p. 5), with `|s|^k` for the printed `s^k`: uniformly over distinct `u, v`,
sets `U ⊇ {u, v}` of size at most `n^{o(1)}` and labellings of `U`,
`P[|N^{(k)}_{u,v} - Y_{u,v}| ≥ |s|^k n^{-4/3} | σ_U] ≤ n^{-1/3+o(1)}` with `k = ⌈α log n⌉`. -/
theorem theorem_2_8_4 (a b : ℕ → ℝ) (ℓ : ℕ → ℕ) (lam α : ℝ)
    (hA : Assumption27 a b ℓ) (hP : Theorem28Params a b lam α) :
    ∀ e : ℕ → ℝ, Tendsto e atTop (𝓝 0) →
      ∃ c : ℕ → ℝ, Tendsto c atTop (𝓝 0) ∧
        ∀ (n : ℕ) (u v : Fin n) (U : Finset (Fin n)) (τ : Fin n → Bool),
          u ≠ v → u ∈ U → v ∈ U → (U.card : ℝ) ≤ (n : ℝ) ^ (e n) →
          condProb n (a n) (b n) U τ (fun _ G =>
              |sPar (a n) (b n)| ^ pathLen α n * (n : ℝ) ^ (-4 / 3 : ℝ) ≤
                |pathN n (a n) (b n) (pathLen α n) u v G -
                  pathY n (a n) (b n) (pathLen α n) u v G|) ≤
            (n : ℝ) ^ (-1 / 3 + c n) := by sorry

end SBMThreshold.Main
