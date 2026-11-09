-- Prove2me | Theorems.Thm_SharpConsist_lemma_B_2
-- name    : SharpConsist.lemma_B_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T12:13:57.922205+00:00
-- url     : https://prove2.me/theorems/30a7d586-fc2a-4e82-aa11-43ab1300de2b
-- title:
--   Lemma B.2 — the discrete oracle is a legal instance with small marginals
-- statement:
--   Fix $T\in[7/5,3/2]$ and an integer $m\ge32$, integers $k\ge1$ and $n=(m+1)k$, and a $k$-set $A\subseteq X=[n]$. The function $f_A$ of Eq. (5.9) on $X\cup\{r\}$ satisfies:
--
--   1. $f_A$ is normalized, monotone and submodular on all subsets of $X\cup\{r\}$, including sets larger than $k$;
--   2. $f_A\ge0$;
--   3. for every current element $e\in X$ and every background $U\subseteq X\cup\{r\}$ with $e\notin U$ (with or without $r$),
--   $$0\le f_A(U\cup\{e\})-f_A(U)\le\frac5k.$$
--
--   This transfers the continuous signs of Lemma B.1 to the full discrete oracle.
--
--   Differences from the source:
--   - encoding: X = [n] and the ground set X ∪ {r} → Fin n, embedded in Fin (n+1) by Fin.castSucc, with r = Fin.last n; reason: 0-based indices; same instances
--   - encoding: monotone: f(i | S) ≥ 0; submodular: f(i | S) ≥ f(i | T) for S ⊆ T → PolyContract.IsRankFunction: f(S ∪ T) + f(S ∩ T) ≤ f S + f T, f ∅ = 0, A ⊆ B → f A ≤ f B; reason: equivalent forms on a finite ground set
-- source:
--   Fu–Zhang–Tao, A Sharp Barrier of Consistent Submodular Maximization, arXiv:2609.09986 (held version, sha256 874ec76c…), Appendix B.3, Lemma B.2, p.37

import Mathlib
import Definitions.Def_SharpConsist_fA
import Definitions.Def_PolyContract_IsRankFunction

namespace SharpConsist

/-- **Lemma B.2 (continuous signs certify the full discrete oracle).** Fu–Zhang–Tao, *A Sharp Barrier of Consistent Submodular Maximization*, arXiv:2609.09986 (held version, sha256 874ec76c…), Appendix B.3,
Lemma B.2, p.37. Fix `T ∈ [7/5, 3/2]`, integers `m ≥ 32`, `k ≥ 1`, `n = (m+1)k`, and a `k`-set
`A ⊆ X`. The function `f_A` of Eq. (5.9) is normalized, nonnegative, monotone and submodular on all
subsets of `X ∪ {r}` (of any size), and every marginal `f_A(U ∪ {e}) − f_A(U)` of a current element
`e ∈ X`, against any background `U ∌ e` (with or without `r`), lies in `[0, 5/k]`.

**Formalization Note.** `X ∪ {r} = Fin (n+1)`, current elements are `Fin.castSucc e`. -/
theorem lemma_B_2 (T : ℝ) (hT : T ∈ Set.Icc (7 / 5 : ℝ) (3 / 2)) (m k n : ℕ) (hm : 32 ≤ m)
    (hk : 1 ≤ k) (hn : n = (m + 1) * k) (A : Finset (Fin n)) (hA : A.card = k) :
    PolyContract.IsRankFunction (fA T m k A) ∧ (∀ U : Finset (Fin (n + 1)), 0 ≤ fA T m k A U) ∧
    ∀ (e : Fin n) (U : Finset (Fin (n + 1))), Fin.castSucc e ∉ U →
      0 ≤ fA T m k A (insert (Fin.castSucc e) U) - fA T m k A U ∧
      fA T m k A (insert (Fin.castSucc e) U) - fA T m k A U ≤ 5 / (k : ℝ) := by sorry

end SharpConsist
