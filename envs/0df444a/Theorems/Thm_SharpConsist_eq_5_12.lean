-- Prove2me | Theorems.Thm_SharpConsist_eq_5_12
-- name    : SharpConsist.eq_5_12
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T12:13:37.604436+00:00
-- url     : https://prove2.me/theorems/98ce2e78-6b6e-46e4-a8b9-307eb0d0863a
-- title:
--   Eq. (5.12) — the value of the pre-arrival output after adjoining $r$
-- statement:
--   Fix $T\in[7/5,3/2]$ and an integer $m\ge32$, integers $k\ge1$, $n=(m+1)k$, $\delta=1/(64m)$, and a $k$-set $A\subseteq X$. For every $S\subseteq X$ with $|S|\le k$ and $|u_A(S)|\le\delta$,
--   $$f_A(S\cup\{r\})\le R(T)+\frac{32}m+32\delta+5\Bigl(\frac1{m+1}+\delta\Bigr)\le R(T)+\frac{38}m.$$
--   In the proof of Theorem 5.1 this is applied to the output $S^-$ before the final arrival on the hiding event: even with $r$ granted for free, a balanced feasible set is worth only about $R(T)$.
--
--   Differences from the source:
--   - generalization: the pre-arrival output S⁻ on the hiding event E → every S ⊆ X with |S| ≤ k and |u_A(S)| ≤ δ; reason: these are the only properties of S⁻ on E that the estimate uses (feasibility and the band)
--   - encoding: X = [n] and the ground set X ∪ {r} → Fin n, embedded in Fin (n+1) by Fin.castSucc, with r = Fin.last n; reason: 0-based indices; same instances
-- source:
--   Fu–Zhang–Tao, A Sharp Barrier of Consistent Submodular Maximization, arXiv:2609.09986 (held version, sha256 874ec76c…), §5.3, proof of Theorem 5.1 ("Before repair"), Eq. (5.12), p.16

import Mathlib
import Definitions.Def_SharpConsist_fA
import Definitions.Def_SharpConsist_uA
import Definitions.Def_SharpConsist_RT

namespace SharpConsist

/-- **Eq. (5.12): the value before repair.** Fu–Zhang–Tao, *A Sharp Barrier of Consistent Submodular
Maximization*, arXiv:2609.09986 (held version, sha256 874ec76c…), §5.3, proof of Theorem 5.1, "Before
repair", Eq. (5.12), p.16. Fix `T ∈ [7/5, 3/2]`, integers `m ≥ 32`, `k ≥ 1`, `n = (m+1)k`, `δ = 1/(64m)`,
and a `k`-set `A ⊆ X`. For every `S ⊆ X` with `|S| ≤ k` and `|u_A(S)| ≤ δ`,
`f_A(S ∪ {r}) ≤ R(T) + 32/m + 32δ + 5(1/(m+1) + δ) ≤ R(T) + 38/m`. -/
theorem eq_5_12 (T : ℝ) (hT : T ∈ Set.Icc (7 / 5 : ℝ) (3 / 2)) (m k n : ℕ) (hm : 32 ≤ m)
    (hk : 1 ≤ k) (hn : n = (m + 1) * k) (A : Finset (Fin n)) (hA : A.card = k)
    (S : Finset (Fin n)) (hS : S.card ≤ k) (hu : |uA k m A S| ≤ deltaM m) :
    fA T m k A (insert (Fin.last n) (embedX S)) ≤
      RT T + 32 / (m : ℝ) + 32 * deltaM m + 5 * (1 / ((m : ℝ) + 1) + deltaM m) ∧
    RT T + 32 / (m : ℝ) + 32 * deltaM m + 5 * (1 / ((m : ℝ) + 1) + deltaM m) ≤
      RT T + 38 / (m : ℝ) := by sorry

end SharpConsist
