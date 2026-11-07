-- Prove2me | Theorems.Thm_RevisitXor_reduction_k_two
-- name    : RevisitXor.reduction_k_two
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T17:04:23.081334+00:00
-- url     : https://prove2.me/theorems/264c74e0-1614-46b9-81b2-e01741d9c979
-- title:
--   Reduction to $k=2$: $\operatorname{corr}(f^{\oplus 2j},p)=\operatorname{corr}(f^{\oplus2},q)^j$ with $p$ quadratic
-- statement:
--   Let $f:[2]^n\to[2]$, let $q$ be a polynomial modulo $2$ of degree at most $2$ in the $2n$ variables of $[2]^{2n}$, and let $j\ge0$. There is a polynomial $p$ modulo $2$ of degree at most $2$ in the $2jn$ variables of $[2]^{2jn}$ with
--
--   $$\operatorname{corr}\big(f^{\oplus 2j},p\big)=\operatorname{corr}\big(f^{\oplus 2},q\big)^{j}.$$
--
--   This is why it suffices to prove Theorem 1 for $k=2$: if $\operatorname{corr}(f^{\oplus2},q)\ge2^{-n/2}$ then $\operatorname{corr}(f^{\oplus k},p)\ge(2^{-n/2})^{k/2}$ for every even $k$.
--
--   **Formalization Note** Variables are indexed by `Fin k × Fin n` and evaluated at $x_j(i)$; $j=0$ is included ($f^{\oplus0}=0$).
--
--   Differences from the source:
--   - reading: "It suffices to prove it for k = 2." (a reduction, with no displayed statement) → for every f, quadratic q in 2n variables and j, a quadratic p in 2jn variables with corr(f^{⊕2j}, p) = corr(f^{⊕2}, q)^j; reason: this is the fact the reduction rests on (correlation is multiplicative over independent blocks, and a sum of quadratics on disjoint blocks is quadratic); together with corr(f^{⊕2}, q) ≥ 2^{−n/2} ≥ 0 it yields clause 3 of Theorem 1 for every even k
-- source:
--   Viola, Revisiting the XOR lemma, STOC 2027 submission (manuscript of August 25, 2026, sha256 3b49e10d…716), §1, p.5

import Mathlib
import Definitions.Def_RevisitXor_corr
import Definitions.Def_RevisitXor_xorPow

namespace RevisitXor

/-- **Reduction to `k = 2`.** Viola, *Revisiting the XOR lemma*, STOC 2027 submission (manuscript of August 25, 2026, sha256
3b49e10d…716), §1, p.5: "It suffices to prove it for k = 2."

For every `f : [2]^n → [2]` and every quadratic polynomial `q` in the `2n` variables of `[2]^{2n}`,
and every `j`, there is a quadratic polynomial `p` in the `2jn` variables of `[2]^{2jn}` with
`corr(f^{⊕2j}, p) = corr(f^{⊕2}, q)^j`.

**Formalization Note.** This is the content of the reduction: correlation is multiplicative over
independent blocks, and a sum of quadratic polynomials on disjoint blocks of variables is quadratic.
With `k = 2j` and `corr(f^{⊕2}, q) ≥ 2^{-n/2}` it gives `corr(f^{⊕k}, p) ≥ (2^{-n/2})^{k/2}`. Variables
are indexed by `Fin k × Fin n` and evaluated at `x j i`; `j = 0` is included. -/
theorem reduction_k_two {n : ℕ} (f : Cube n → ZMod 2)
    (q : MvPolynomial (Fin 2 × Fin n) (ZMod 2)) (hq : q.totalDegree ≤ 2) (j : ℕ) :
    ∃ p : MvPolynomial (Fin (2 * j) × Fin n) (ZMod 2), p.totalDegree ≤ 2 ∧
      corr (xorPow f (2 * j)) (fun x => MvPolynomial.eval (fun ji => x ji.1 ji.2) p) =
        corr (xorPow f 2) (fun x => MvPolynomial.eval (fun ji => x ji.1 ji.2) q) ^ j := by sorry

end RevisitXor
