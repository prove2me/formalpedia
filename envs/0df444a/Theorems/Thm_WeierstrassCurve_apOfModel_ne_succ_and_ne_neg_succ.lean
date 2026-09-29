-- Prove2me | Theorems.Thm_WeierstrassCurve_apOfModel_ne_succ_and_ne_neg_succ
-- name    : WeierstrassCurve.apOfModel_ne_succ_and_ne_neg_succ
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.363612+00:00
-- url     : https://prove2.me/theorems/6437634a-4abc-531b-8b20-8bde4553b249
-- title:
--   a_q of an integral Weierstrass model is never ±(q+1)
-- statement:
--   Let $W$ be a Weierstrass curve over $\mathbb Z$, i.e. a tuple $(a_1,a_2,a_3,a_4,a_6)$ of integers, and let $q$ be a prime number. Write $\widetilde W$ for [`WeierstrassCurve.reductionMod`](def/FLTPrelim_Modularity.html#L76), the Weierstrass curve over $\mathbb{Z}/q\mathbb{Z}$ obtained by applying the canonical ring homomorphism $\mathbb Z \to \mathbb Z/q\mathbb Z$ to the coefficients, and let [`WeierstrassCurve.apOfModel`](def/FLTPrelim_Modularity.html#L79) of $W$ at $q$ be the quantity [`WeierstrassCurve.traceOfFrobenius`](def/FLTPrelim_Modularity.html#L72) of $\widetilde W$, namely $\#(\mathbb Z/q\mathbb Z) + 1 - \#\widetilde W$, where $\#\widetilde W$ is the cardinality of the point set of the associated affine curve (the point at infinity together with all solutions of the Weierstrass equation over $\mathbb Z/q\mathbb Z$, in the sense of Mathlib's [`WeierstrassCurve.card`](def/FLTPrelim_Modularity.html#L70)). The assertion is the conjunction of two inequalities of integers: this quantity is distinct from $q+1$ and distinct from $-(q+1)$. Equivalently, the point count satisfies $1 \le \#\widetilde W \le 2q+1$. No smoothness or good-reduction hypothesis on $\widetilde W$ is imposed, and no Hasse bound is asserted.
--
--   This is the elementary bound on the number of points of the reduction of a Weierstrass model modulo a prime, far weaker than the Hasse–Weil estimate $|a_q| \le 2\sqrt q$ but valid without any hypothesis of good reduction. It is used in the conductor-level bookkeeping, via [`WeierstrassCurve.prime_dvd_discr_and_not_sq_dvd_of_localType`](thm.html#WeierstrassCurve.prime_dvd_discr_and_not_sq_dvd_of_localType), to exclude the value $\pm(q+1)$ for the Frobenius trace at a prime $q$, as occurs for a form new at a prime exactly dividing its level.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_apOfModel_ne_succ_and_ne_neg_succ.lean

import Definitions.Def_FLTPrelim_Modularity

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem WeierstrassCurve.apOfModel_ne_succ_and_ne_neg_succ (W : WeierstrassCurve ℤ) {q : ℕ} (hq : q.Prime) :
    W.apOfModel q ≠ (q : ℤ) + 1 ∧ W.apOfModel q ≠ -((q : ℤ) + 1) := by sorry
