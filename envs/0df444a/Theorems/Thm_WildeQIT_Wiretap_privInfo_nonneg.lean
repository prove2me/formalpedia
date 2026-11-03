-- Prove2me | Theorems.Thm_WildeQIT_Wiretap_privInfo_nonneg
-- name    : WildeQIT.Wiretap.privInfo_nonneg
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T04:28:38.645195+00:00
-- url     : https://prove2.me/theorems/ef27793d-3f04-4cd2-90e2-f3d6447c0fc0
-- title:
--   Private information is non-negative: $P(N)\ge 0$
-- statement:
--   **Property 13.2.1.** The private information of a classical wiretap channel $N\equiv p_{Y,Z|X}$ is non-negative:
--
--   $$
--   P(N)\ge 0 .
--   $$
--
--   Although $P(N)$ is defined as a maximum of a difference of two mutual informations, the difference can always be made zero, so the maximum is never negative.
--
--   **Formalization Note** Alphabets are finite types (the book's setting) and information is measured in bits ($\log_2$). Distributions are the published `WildeQIT.FinDist`, channels the published `WildeQIT.Channel`, and $I(\cdot\,;\cdot)$ is the published `WildeQIT.mutualInfo` of a joint distribution (first component against second). No nonemptiness assumption is needed: for an empty input alphabet Lean's value is $0$, which also satisfies the bound.
--
--   Differences from the source:
--   - encoding: P(N) ≡ max_{p_{U,X}} [I(U;Y) − I(U;Z)] over auxiliary U of any alphabet (13.57) → privInfo N, the supremum over U with alphabet Fin n for every n ∈ ℕ; reason: every finite alphabet is in bijection with some Fin n and mutual information is invariant under relabeling; the book does not prove attainment, so its max is read as the supremum of the same set
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, Property 13.2.1, eq. (13.58), p. 397

import Definitions.Def_WildeQIT_Wiretap_privInfo

namespace WildeQIT.Wiretap

open WildeQIT

/-- **Property 13.2.1 (non-negativity of private information).**
Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8, Property 13.2.1, (13.58),
p. 397: the private information `P(N)` of a wiretap channel is non-negative, `P(N) ≥ 0`.

**Formalization Note.** `P(N)` is `privInfo N`, the supremum over all finite auxiliary
alphabets. No nonemptiness assumption is needed: for an empty input alphabet the value is the
junk `0`, which also satisfies the bound. -/
theorem privInfo_nonneg {α β γ : Type} [Fintype α] [Fintype β] [Fintype γ]
    (N : WiretapChannel α β γ) : 0 ≤ privInfo N := by sorry

end WildeQIT.Wiretap
