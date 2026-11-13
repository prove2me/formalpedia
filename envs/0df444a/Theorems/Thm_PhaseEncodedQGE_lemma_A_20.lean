-- Prove2me | Theorems.Thm_PhaseEncodedQGE_lemma_A_20
-- name    : PhaseEncodedQGE.lemma_A_20
-- status  : Open
-- author  : @iris
-- created : 2026-11-12T06:50:55.702932+00:00
-- url     : https://prove2.me/theorems/eade2880-081e-41ce-9e93-2eeaa66b27c1
-- title:
--   Lemma A.20 — $1,\sin^2\gamma,t^2,t^2\sin^2\gamma$ are $\mathbb Q$-linearly independent at the schedule
-- statement:
--   At $\eta=23/8$ and $\gamma=2$, with $t=\tan(\eta/2)=\tan(23/16)$, the four real numbers
--   $$1,\qquad\sin^2 2,\qquad t^2,\qquad t^2\sin^2 2$$
--   are linearly independent over $\mathbb Q$.
--
--   This is the hypothesis of the Y-mixer determination theorem (Theorem A.21) at the schedule.
--
--   **Formalization Note** $\mathbb R$ is regarded as a $\mathbb Q$-vector space.
--
--   Differences from the source: none.
-- source:
--   Miller, Lee, Structural Accessibility in Phase-Encoded Quantum Graph Embeddings, STOC 2027 submission (build 2026-11-03, sha256 f1132658…7c51), App. A.1.6, p.21 (PDF p.22), Lemma A.20

import Mathlib
import Definitions.Def_PhaseEncodedQGE_Profile
set_option autoImplicit false

namespace PhaseEncodedQGE

open Matrix

/-- Lemma A.20, rational independence at the schedule (Miller, Lee, *Structural Accessibility in Phase-Encoded Quantum Graph Embeddings*, STOC 2027 submission (build 2026-11-03), App. A.1.6, p.21).

At `η = 23/8` and `γ = 2` the four numbers `1, sin² γ, t²` and `t² sin² γ` (with `t = tan(η/2)`) are
linearly independent over `ℚ`.

**Formalization Note** `ℝ` is a `ℚ`-vector space; the four numbers are the family `![…] : Fin 4 → ℝ`. -/
theorem lemma_A_20 :
    LinearIndependent ℚ ![(1 : ℝ), Real.sin 2 ^ 2, Real.tan ((23 / 8 : ℝ) / 2) ^ 2,
      Real.tan ((23 / 8 : ℝ) / 2) ^ 2 * Real.sin 2 ^ 2] := by sorry

end PhaseEncodedQGE
