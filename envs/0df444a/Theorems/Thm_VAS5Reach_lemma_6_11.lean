-- Prove2me | Theorems.Thm_VAS5Reach_lemma_6_11
-- name    : VAS5Reach.lemma_6_11
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T22:30:43.43814+00:00
-- url     : https://prove2.me/theorems/2c9c145d-03e9-4c38-97bc-f0b09f82ab88
-- title:
--   Lemma 6.11 — $\mathbb Z$-runs can be shortened to length $(\mathrm{SIZE}(U) + \|x\| + \|y\|)^{\mathrm{poly}(d)}$
-- statement:
--   There is a constant $c$ such that the following holds. Let $U = (Q, T)$ be a $d$-VASS. If $p(x) \xrightarrow{*}_{\mathbb Z} q(y)$ in $U$, then there is such a $\mathbb Z$-run of length at most
--   $$
--   \bigl(\mathrm{SIZE}(U) + \|x\| + \|y\|\bigr)^{c(d+1)^c}.
--   $$
--
--   Differences from the source:
--   - encoding: exponent poly(d) → c·(d + 1)^c with one constant c quantified before d and every instance; reason: every polynomial in d is bounded by c(d + 1)^c for a suitable c
-- source:
--   Chen, Fu, Fu, Reachability in Five-Dimensional Vector Addition Systems Is PSPACE-Complete, arXiv:2610.40012 (held version, sha256 a74d76f9…), Lemma 6.11, p.28 (PDF p.30); proof App. D.4, p.50 (PDF p.52)

import Mathlib
import Definitions.Def_VAS5Reach_supNorm
import Definitions.Def_VAS5Reach_VASS
import Definitions.Def_VAS5Reach_VASS_IsRun

namespace VAS5Reach

/-- **Lemma 6.11.** Let `U = (Q, T)` be a `d`-VASS. If `p(x) −∗→_Z q(y)` in `U`, there is such a
`ℤ`-run of length at most `(SIZE(U) + ∥x∥ + ∥y∥)^{poly(d)}`.

Source: W. Chen, B. Fu, Y. Fu, *Reachability in Five-Dimensional Vector Addition Systems Is
PSPACE-Complete*, arXiv:2610.40012 (held version, sha256 a74d76f9…), Lemma 6.11, printed p. 28 (PDF p. 30); proof in App. D.4, printed p. 50.

**Formalization Note** `d = Fintype.card ι`; `poly(d)` is `c(d + 1)^c` with one `c` quantified
before `d` and every instance. `x`, `y` are `ℤ`-configurations' vectors (the paper's `ℤ`-runs are
between `ℤ`-configurations). -/
theorem lemma_6_11 :
    ∃ c : ℕ, ∀ (d : ℕ) {ι Q : Type} [Fintype ι], Fintype.card ι = d →
      ∀ (U : VASS Q ι) (p q : Q) (x y : ι → ℤ), U.ZReach p x q y →
      ∃ π, U.IsZRun p x π q y ∧
        π.length ≤ (U.size + supNorm x + supNorm y) ^ (c * (d + 1) ^ c) := by sorry

end VAS5Reach
