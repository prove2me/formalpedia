-- Prove2me | Theorems.Thm_ShallowSym_eq_1
-- name    : ShallowSym.eq_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:59:52.280658+00:00
-- url     : https://prove2.me/theorems/d130cf68-2cb0-45f2-a3ef-bc4709dd136f
-- title:
--   Eq. (1): every symmetric function is $\bigvee_{t\in S}1[|x|=t]$
-- statement:
--   Let $f:\{0,1\}^n\to\{0,1\}$ be symmetric. Then there is a set $S\subseteq\{0,1,\dots,n\}$ such that
--
--   $$f(x) = \bigvee_{t\in S} 1\big[|x| = t\big] \qquad\text{for all } x\in\{0,1\}^n.$$
--
--   This decomposition reduces the construction of circuits for symmetric functions to the exact-weight functions $\mathrm{EXACT}_t(x)=1[|x|=t]$.
--
--   Differences from the source:
--   - encoding: ⋁_{t∈S} 1[|x| = t] → decide (|x| ∈ S) with S a Finset ℕ contained in range (n + 1); reason: the same Boolean function
-- source:
--   Lecomte, Ramakrishnan, Optimal Shallow Circuits for Majority, arXiv:2609.34029 (version of 2026-11-01, sha256 6f46ce49…), §2 'Functions', eq. (1), pp.4–5

import Mathlib
import Definitions.Def_ShallowSym_IsSymmetric

namespace ShallowSym

/-- §2 "Functions", eq. (1), pp.4–5. V. Lecomte, P. Ramakrishnan, *Optimal Shallow Circuits for Majority*, arXiv:2609.34029
(version of 2026-11-01, sha256 6f46ce49…).

"In general, any symmetric function can be written as ⋁_{t∈S} 1[|x| = t] (1) for a set
S ⊆ {0, 1, . . . , n}."

Every symmetric `f : {0,1}^n → {0,1}` equals `x ↦ 1[|x| ∈ S]` for some `S ⊆ {0, 1, …, n}`. -/
theorem eq_1 (n : ℕ) (f : Cube n → Bool) (hf : IsSymmetric f) :
    ∃ S : Finset ℕ, S ⊆ Finset.range (n + 1) ∧ ∀ x, f x = decide (weight x ∈ S) := by sorry

end ShallowSym
