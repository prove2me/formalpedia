-- Prove2me | Theorems.Thm_SuperRamanujan227_Main_claim_5_5
-- name    : SuperRamanujan227.Main.claim_5_5
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-08T09:35:37.811663+00:00
-- url     : https://prove2.me/theorems/6638b429-74a8-4176-b516-b31e6ff26b06
-- title:
--   Claim 5.5 — $Q_{n,d}$ is a nonzero multiple of $P_n^{(\alpha,\alpha)}$
-- statement:
--   Let $n\ge2$ and $d\ge3$ be integers with $nd$ even, and let $Q_{n,d}(x)=\frac{\partial^{n(d-1)}}{\partial x^{n(d-1)}}(x^2-1)^{nd/2}$. With $\alpha=n(d-2)/2$ there is a real number $c\ne0$ such that
--   $$Q_{n,d}=c\,P_n^{(\alpha,\alpha)}.$$
--
--   This identification of the configuration-model polynomial with a symmetric Jacobi polynomial is the observation that gives access to precise bounds on its largest root.
--
--   Differences from the source:
--   - reading: Claim 5.5 stated without explicit hypotheses, in the proof of Theorem 1.1 (n even, d ≥ 3), and invoked in the proof of Claim 5.6 (d ≥ 3, n ≥ 2, nd even) → n ≥ 2, d ≥ 3, nd even; reason: the domain on which the paper uses it; Q_{n,d} with m = nd/2 requires nd even
--   - encoding: P_n^(α,α) characterized up to a nonzero scalar → the classical normalization of the Jacobi polynomial; reason: a nonzero scalar multiple of one normalization is one of any other; the existential over c absorbs it
-- source:
--   Gil Cohen, Gal Maor, Quantitative Results on Super-Ramanujan Graphs, STOC 2027 submission #227 (October 2026), SHA-256 1ba5eacb267c8a63eff5e5b9d6b96d9f2b04d5a1e147d887b9e61574127831f8, Claim 5.5, p. 19

import Mathlib
import Definitions.Def_SuperRamanujan227_Main_Jacobi
open Polynomial

namespace SuperRamanujan227.Main

/-- Claim 5.5 (p. 19): `Q_{n,d}` is a nonzero scalar multiple of `P_n^{(α,α)}`, `α = n(d-2)/2`,
on the domain `n ≥ 2`, `d ≥ 3`, `nd` even where it is used (Claim 5.6, p. 20). -/
theorem claim_5_5 (n d : ℕ) (hn : 2 ≤ n) (hd : 3 ≤ d) (hnd : Even (n * d)) :
    ∃ c : ℝ, c ≠ 0 ∧ Q n d = C c * jacobiSym ((n : ℝ) * ((d : ℝ) - 2) / 2) n := by sorry

end SuperRamanujan227.Main
