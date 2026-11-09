-- Prove2me | Theorems.Thm_SharpConsist_repair_gain
-- name    : SharpConsist.repair_gain
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T12:14:04.612791+00:00
-- url     : https://prove2.me/theorems/1f69cf6c-de99-4091-975d-37e7dc201afb
-- title:
--   Gain from repair (proof of Theorem 5.1)
-- statement:
--   Fix $T\in[7/5,3/2]$ and an integer $m\ge32$, integers $k\ge1$, $n=(m+1)k$, and a $k$-set $A\subseteq X$. For all $S^-\subseteq X$, $S^+\subseteq X\cup\{r\}$ and $C\in\mathbb N$ with $|S^+\triangle S^-|\le C$,
--   $$f_A(S^+)\le f_A(S^-\cup\{r\})+\frac{5C}k.$$
--   No restriction is placed on how $S^+$ is computed, so the bound allows unrestricted queries and computation after the final arrival.
--
--   Differences from the source:
--   - generalization: the outputs S⁻ = S_n and S⁺ = S_{n+1} of the algorithm → arbitrary S⁻ ⊆ X and S⁺ ⊆ X ∪ {r} with |S⁺ △ S⁻| ≤ C; reason: the estimate uses only the recourse bound
--   - encoding: X = [n] and the ground set X ∪ {r} → Fin n, embedded in Fin (n+1) by Fin.castSucc, with r = Fin.last n; reason: 0-based indices; same instances
-- source:
--   Fu–Zhang–Tao, A Sharp Barrier of Consistent Submodular Maximization, arXiv:2609.09986 (held version, sha256 874ec76c…), §5.3, proof of Theorem 5.1 ("Gain from repair"), p.17

import Mathlib
import Definitions.Def_SharpConsist_fA

namespace SharpConsist

/-- **Gain from repair.** Fu–Zhang–Tao, *A Sharp Barrier of Consistent Submodular Maximization*,
arXiv:2609.09986 (held version, sha256 874ec76c…), §5.3, proof of Theorem 5.1, "Gain from repair",
p.17. Fix `T ∈ [7/5, 3/2]`, integers `m ≥ 32`, `k ≥ 1`, `n = (m+1)k`, and a `k`-set `A ⊆ X`. If
`S⁻ ⊆ X`, `S⁺ ⊆ X ∪ {r}` and `|S⁺ △ S⁻| ≤ C`, then `f_A(S⁺) ≤ f_A(S⁻ ∪ {r}) + 5C/k`. No restriction
is placed on how `S⁺` was computed. -/
theorem repair_gain (T : ℝ) (hT : T ∈ Set.Icc (7 / 5 : ℝ) (3 / 2)) (m k n : ℕ) (hm : 32 ≤ m)
    (hk : 1 ≤ k) (hn : n = (m + 1) * k) (A : Finset (Fin n)) (hA : A.card = k)
    (Sminus : Finset (Fin n)) (Splus : Finset (Fin (n + 1))) (C : ℕ)
    (hC : (symmDiff Splus (embedX Sminus)).card ≤ C) :
    fA T m k A Splus ≤ fA T m k A (insert (Fin.last n) (embedX Sminus)) + 5 * (C : ℝ) / (k : ℝ) := by sorry

end SharpConsist
