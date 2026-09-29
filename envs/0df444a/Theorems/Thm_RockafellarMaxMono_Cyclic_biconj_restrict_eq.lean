-- Prove2me | Theorems.Thm_RockafellarMaxMono_Cyclic_biconj_restrict_eq
-- name    : RockafellarMaxMono.Cyclic.biconj_restrict_eq
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T00:14:04.599474+00:00
-- url     : https://prove2.me/theorems/d6088cfb-ba09-43b6-a821-129d8741b86a
-- title:
--   §2, p. 211 — the restriction of $f^{**}$ to $E$ is $f$
-- statement:
--   Let $E$ be a real Banach space with bidual $E^{**}$, and let $f$ be a lower semicontinuous proper convex function on $E$. Let $f^{**} = (f^*)^*$ be the biconjugate, a function on $E^{**}$. Then
--
--   $$
--   f^{**}(x) = f(x) \qquad \text{for every } x \in E ,
--   $$
--
--   where $E$ is regarded as a subspace of $E^{**}$ through the canonical embedding.
--
--   At the end of the proof of Theorem B this identity, applied to $f + j$ and $g + j$, carries the relation $(g+j)^{**} = (f+j)^{**} - \alpha$ back to $E$.
--
--   **Formalization Note** The canonical embedding is `NormedSpace.inclusionInDoubleDual ℝ E`. $E$ is not assumed reflexive.
-- source:
--   Rockafellar, On the maximal monotonicity of subdifferential mappings, Pacific J. Math. 33 (1970), p. 211, §2 (citing Moreau [3, §6])

import Mathlib
import Definitions.Def_RockafellarMaxMono_Shared_ProperConvex
import Definitions.Def_RockafellarMaxMono_Shared_Conj

namespace RockafellarMaxMono.Cyclic

theorem biconj_restrict_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (f : E → EReal) (hf : Shared.ProperConvex f) (hlsc : LowerSemicontinuous f) :
    ∀ x : E, Shared.conj (Shared.conj f) (NormedSpace.inclusionInDoubleDual ℝ E x) = f x := by sorry

end RockafellarMaxMono.Cyclic
