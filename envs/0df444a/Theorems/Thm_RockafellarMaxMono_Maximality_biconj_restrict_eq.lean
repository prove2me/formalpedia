-- Prove2me | Theorems.Thm_RockafellarMaxMono_Maximality_biconj_restrict_eq
-- name    : RockafellarMaxMono.Maximality.biconj_restrict_eq
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T18:02:59.589931+00:00
-- url     : https://prove2.me/theorems/79c2c37a-3703-42df-852d-458c885c1d11
-- title:
--   §2, p. 211 — the restriction of $f^{**}$ to $E$ is $f$
-- statement:
--   Let $E$ be a real Banach space, regarded as a subspace of its bidual $E^{**}$ through the canonical embedding $x \mapsto \hat x$, $\hat x(x^*) = \langle x, x^* \rangle$. If $f$ is a lower semicontinuous proper convex function on $E$, then the biconjugate $f^{**} = (f^*)^*$, a function on $E^{**}$, satisfies
--
--   $$
--   f^{**}(\hat x) = f(x) \qquad \text{for every } x \in E .
--   $$
--
--   This is the Fenchel–Moreau theorem in the Banach-space setting, which the paper cites from Moreau. It is used, together with (2.2) and (2.4), to relate $\partial f$ and $\partial f^*$.
--
--   **Formalization Note** The canonical embedding is Mathlib's `NormedSpace.inclusionInDoubleDual ℝ E`. $E$ is not assumed reflexive.
-- source:
--   Rockafellar, On the maximal monotonicity of subdifferential mappings, Pacific J. Math. 33 (1970), p. 211, §2

import Mathlib
import Definitions.Def_RockafellarMaxMono_Shared_ProperConvex
import Definitions.Def_RockafellarMaxMono_Shared_Conj

namespace RockafellarMaxMono.Maximality

theorem biconj_restrict_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (f : E → EReal) (hf : Shared.ProperConvex f) (hlsc : LowerSemicontinuous f) :
    ∀ x : E, Shared.conj (Shared.conj f) (NormedSpace.inclusionInDoubleDual ℝ E x) = f x := by sorry

end RockafellarMaxMono.Maximality
