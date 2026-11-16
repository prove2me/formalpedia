-- Prove2me | Theorems.Thm_SFMQueryLower_EmptyMin_Supplement_lemma_C_5
-- name    : SFMQueryLower.EmptyMin.Supplement.lemma_C_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T17:28:49.452991+00:00
-- url     : https://prove2.me/theorems/c11aeaa3-77fb-4be4-834d-83e7ec6b1ec9
-- title:
--   Lemma C.5 — one CGJS value query answers one prefix query, without knowing $\pi$
-- statement:
--   Let $k\ge1$ and $n=2k$. For a permutation $\pi$ of $[n]$ let $z^\pi\in\{0,1\}^n$ and $\sigma^\pi$ be the string and permutation of Lemma C.5: $z^\pi_{p_i^\pi}=1$, $z^\pi_{r_i^\pi}=0$, $\sigma^\pi(2(k-i)+1)=p_i^\pi$ and $\sigma^\pi(2(k-i)+2)=r_i^\pi$ for $i\in[k]$.
--
--   For every query string $x\in\{0,1\}^n$ there is a deterministic value-oracle procedure $B_x$, fixed before $\pi$, such that for every permutation $\pi$ of $[n]$, run on the value oracle of $h_k^\pi$, it makes at most one value query and returns
--   $$\operatorname{prefix-len}_{z^\pi,\sigma^\pi}(x).$$
--
--   This makes every value oracle in $\mathcal F$ a prefix oracle of a $\mathrm{HiddenPermutation}_n$ instance, which is how the upper bound of Theorem C.6 runs a hidden-permutation algorithm.
--
--   **Formalization Note** Procedures are the published deterministic `OracleStrategy` with real replies; the query count includes every issued query.
--
--   Differences from the source:
--   - encoding: "we can compute $\operatorname{prefix-len}_{z,\sigma}(x)$ using one value-oracle query to $h_k^\pi$, without knowing $\pi$" → for each $x$ there exists a deterministic strategy, quantified before $\pi$, that returns the value on every $h_k^\pi$ with at most one issued query; reason: quantifying the procedure before $\pi$ is the meaning of "without knowing $\pi$".
-- source:
--   James Fox, Randomized Query Lower Bounds for Submodular Function Minimization, STOC 2027 submission #292 (October 2026), Lemma C.5, printed p. 21 / PDF p. 22 (proof printed pp. 21–22 / PDF pp. 22–23)

import Definitions.Def_SFMQueryLower_EmptyMin_OracleStrategy
import Definitions.Def_SFMQueryLower_EmptyMin_Supplement_CGJSEncoding

set_option autoImplicit false
open scoped ENNReal

namespace SFMQueryLower.EmptyMin.Supplement

/-- Fox, Lemma C.5, printed p. 21 / PDF p. 22 (proof pp. 21–22 / PDF pp. 22–23).
`n = 2k`. For every prefix query `x`, a deterministic value-oracle procedure `B`, fixed before
the hidden permutation `π` ("without knowing π"), returns `prefix-len_{z,σ}(x)` for the string
`z = simString π` and permutation `σ = simPerm π` displayed in the lemma, using at most one
value query to `h_k^π`. -/
theorem lemma_C_5 (k : ℕ) (hk : 0 < k) (x : Fin (2 * k) → Bool) :
    ∃ B : OracleStrategy (Finset (Fin (2 * k))) ℝ ℕ,
      ∀ π : Equiv.Perm (Fin (2 * k)),
        Returns B (cgjsFunction π) (prefixLen (simString π) (simPerm π) x) ∧
        queryCount B (cgjsFunction π) (fun _ => True) ≤ 1 := by sorry

end SFMQueryLower.EmptyMin.Supplement
