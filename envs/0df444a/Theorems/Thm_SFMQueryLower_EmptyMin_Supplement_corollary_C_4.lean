-- Prove2me | Theorems.Thm_SFMQueryLower_EmptyMin_Supplement_corollary_C_4
-- name    : SFMQueryLower.EmptyMin.Supplement.corollary_C_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T17:29:59.78227+00:00
-- url     : https://prove2.me/theorems/3308be0c-7e5b-498a-97e1-25b7c6a50d64
-- title:
--   Corollary C.4 — recovering the hidden string needs $\Omega(k\log\log k)$ expected prefix queries
-- statement:
--   There is an absolute constant $c>0$ such that the following holds for every $k\ge2$. Let $A$ be a randomized algorithm that queries $\operatorname{prefix-len}_{z,\sigma}$ and, on every $\mathrm{HiddenPermutation}_k$ instance $(z,\sigma)$, returns $z$ with probability $1$ (zero error). Then there is a fixed instance $(z,\sigma)$ on which
--   $$\mathbb E\bigl[Q(A,\operatorname{prefix-len}_{z,\sigma})\bigr]\ge c\,k\log\log k.$$
--
--   The algorithm need not recover $\sigma$. The corollary is the hidden-permutation lower bound that Theorem C.9 transfers to the CGJS family.
--
--   **Formalization Note** The algorithm is a published `RandomizedOracle` with queries in $\{0,1\}^k$ and natural-number replies; expectations are in $[0,\infty]$. For $k=2$, $\log\log 2<0$ and the bound is read as $0$ (`ENNReal.ofReal` of a negative number). The cited Theorem C.3 [AAD+13] is not a hypothesis.
--
--   Differences from the source:
--   - encoding: $\Omega(k\log\log k)$ expected prefix queries on some instance → one absolute constant $c$ with the bound for every $k\ge2$; reason: for $k\ge3$, $k\log\log k>0$ and every zero-error algorithm makes at least $1/2$ expected query on some instance (with no query its output does not depend on $z$), so the eventual and the all-$k$ forms are equivalent; at $k=2$ the bound is $0$.
-- source:
--   James Fox, Randomized Query Lower Bounds for Submodular Function Minimization, STOC 2027 submission #292 (October 2026), Corollary C.4, printed p. 21 / PDF p. 22

import Definitions.Def_SFMQueryLower_EmptyMin_RandomizedOracle
import Definitions.Def_SFMQueryLower_EmptyMin_Supplement_HiddenPermutation

set_option autoImplicit false
open scoped ENNReal

namespace SFMQueryLower.EmptyMin.Supplement

/-- Fox, Corollary C.4, printed p. 21 / PDF p. 22. The constant `c` precedes `k` and the
algorithm. A zero-error algorithm returns the hidden string `z` with probability exactly `1`
on every `HiddenPermutation_k` instance `(z, σ)`; it then makes at least `c k log log k`
expected prefix queries on some fixed instance. The cited Theorem C.3 is not a hypothesis. -/
theorem corollary_C_4 :
    ∃ c : ℝ, 0 < c ∧ ∀ k : ℕ, 2 ≤ k →
      ∀ A : RandomizedOracle (Fin k → Bool) ℕ (Fin k → Bool),
        (∀ (z : Fin k → Bool) (σ : Equiv.Perm (Fin k)),
          A.law {ω | Returns (A.choose ω) (prefixLen z σ) z} = 1) →
        ∃ (z : Fin k → Bool) (σ : Equiv.Perm (Fin k)),
          ENNReal.ofReal (c * (k : ℝ) * Real.log (Real.log (k : ℝ))) ≤
            expectedCount A (prefixLen z σ) (fun _ => True) := by sorry

end SFMQueryLower.EmptyMin.Supplement
