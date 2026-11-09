-- Prove2me | Theorems.Thm_SharpConsist_eq_5_10_reference_valid
-- name    : SharpConsist.eq_5_10_reference_valid
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T12:13:58.698431+00:00
-- url     : https://prove2.me/theorems/d6d4139f-306f-4587-ad21-ac56cdb1a5e1
-- title:
--   Eq. (5.10) — the reference instance is a legal instance
-- statement:
--   Fix $T\in[7/5,3/2]$ and an integer $m\ge32$, integers $k\ge1$ and $n=(m+1)k$. The reference function $f_{\mathrm{ref}}(U)=\psi(|U\cap X|/k)$ on $X\cup\{r\}$ is normalized, monotone and submodular, and $r$ has zero marginal:
--   $$f_{\mathrm{ref}}(U\cup\{r\})=f_{\mathrm{ref}}(U)\quad\text{for all }U\subseteq X\cup\{r\}.$$
--   Its validity lets the algorithm's query bound and termination apply to the reference execution.
--
--   Differences from the source:
--   - encoding: X = [n] and the ground set X ∪ {r} → Fin n, embedded in Fin (n+1) by Fin.castSucc, with r = Fin.last n; reason: 0-based indices; same instances
--   - encoding: monotone: f(i | S) ≥ 0; submodular: f(i | S) ≥ f(i | T) for S ⊆ T → PolyContract.IsRankFunction: f(S ∪ T) + f(S ∩ T) ≤ f S + f T, f ∅ = 0, A ⊆ B → f A ≤ f B; reason: equivalent forms on a finite ground set
-- source:
--   Fu–Zhang–Tao, A Sharp Barrier of Consistent Submodular Maximization, arXiv:2609.09986 (held version, sha256 874ec76c…), §5.2, Eq. (5.10), p.15; Appendix B.4, p.37

import Mathlib
import Definitions.Def_SharpConsist_fref
import Definitions.Def_PolyContract_IsRankFunction

namespace SharpConsist

/-- **Eq. (5.10): the reference instance is a model instance.** Fu–Zhang–Tao, *A Sharp Barrier of
Consistent Submodular Maximization*, arXiv:2609.09986 (held version, sha256 874ec76c…), §5.2, p.15
(and Appendix B.4, p.37). Fix `T ∈ [7/5, 3/2]`, integers `m ≥ 32`, `k ≥ 1`, `n = (m+1)k`. The function
`f_ref(U) = ψ(|U ∩ X|/k)` on `X ∪ {r}` is normalized, monotone and submodular, and `r` has zero
marginal: `f_ref(U ∪ {r}) = f_ref(U)`. -/
theorem eq_5_10_reference_valid (T : ℝ) (hT : T ∈ Set.Icc (7 / 5 : ℝ) (3 / 2)) (m k n : ℕ)
    (hm : 32 ≤ m) (hk : 1 ≤ k) (hn : n = (m + 1) * k) :
    PolyContract.IsRankFunction (fref T m k (n := n)) ∧
    ∀ U : Finset (Fin (n + 1)), fref T m k (insert (Fin.last n) U) = fref T m k U := by sorry

end SharpConsist
