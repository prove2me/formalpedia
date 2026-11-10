-- Prove2me | Theorems.Thm_VAS5Reach_lemma_6_13
-- name    : VAS5Reach.lemma_6_13
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T22:29:50.928518+00:00
-- url     : https://prove2.me/theorems/7e278352-6569-4274-9c2c-23b992f43197
-- title:
--   Lemma 6.13 — in a wide sequential VASS, covering configurations are $\mathbb Z$-connected
-- statement:
--   Let $U = (U_1)u_1\cdots u_{k-1}(U_k)$ be a wide sequential VASS with $p$ in $U_1$ and $q$ in $U_k$. Suppose that
--   $$
--   p(x) \xrightarrow{\alpha}_{\mathbb Z} p(u), \qquad p(x) \xrightarrow{*}_{\mathbb Z} q(y), \qquad q(v) \xrightarrow{\beta}_{\mathbb Z} q(y)
--   $$
--   in $U$. Then $p(u) \xrightarrow{*}_{\mathbb Z} q(v)$ in $U$. It is used in the proof of Theorem 6.10 to connect the configurations produced by Rackoff's covering runs.
--
--   Differences from the source: none.
-- source:
--   Chen, Fu, Fu, Reachability in Five-Dimensional Vector Addition Systems Is PSPACE-Complete, arXiv:2610.40012 (held version, sha256 a74d76f9…), Lemma 6.13, p.28 (PDF p.30)

import Mathlib
import Definitions.Def_VAS5Reach_VASS_IsRun
import Definitions.Def_VAS5Reach_VASS_cycleSpace
import Definitions.Def_VAS5Reach_VASS_IsSeqDecomp

namespace VAS5Reach

/-- **Lemma 6.13.** Let `U = (U₁)u₁ ⋯ u_{k−1}(U_k)` be wide, with `p` in `U₁` and `q` in `U_k`.
Suppose that `p(x) −α→_Z p(u)`, `p(x) −∗→_Z q(y)`, `q(v) −β→_Z q(y)` in `U`. Then
`p(u) −∗→_Z q(v)` in `U`.

Source: W. Chen, B. Fu, Y. Fu, *Reachability in Five-Dimensional Vector Addition Systems Is
PSPACE-Complete*, arXiv:2610.40012 (held version, sha256 a74d76f9…), Lemma 6.13, printed p. 28 (PDF p. 30).

**Formalization Note** `U` is a sequential VASS (`IsSequential U p q`: `p` in the first, `q` in
the last component) of any dimension; `x, u, v, y` are `ℤ`-configurations' vectors (the
conclusion is a `ℤ`-run). -/
theorem lemma_6_13 {ι Q : Type} (U : VASS Q ι) (p q : Q) (hseq : U.IsSequential p q)
    (hwide : U.IsWide) (x u v y : ι → ℤ) (hα : U.ZReach p x p u) (hxy : U.ZReach p x q y)
    (hβ : U.ZReach q v q y) : U.ZReach p u q v := by sorry

end VAS5Reach
