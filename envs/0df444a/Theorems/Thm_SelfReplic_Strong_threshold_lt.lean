-- Prove2me | Theorems.Thm_SelfReplic_Strong_threshold_lt
-- name    : SelfReplic.Strong.threshold_lt
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T01:21:54.144529+00:00
-- url     : https://prove2.me/theorems/2da0725d-3f6f-46fe-a90a-237a8a2fff8a
-- title:
--   Theorem 1 (preamble), p. 10 — the thresholds satisfy $\underline I < \overline I$
-- statement:
--   Consider the base model under the standing assumptions and Strong Replicability. Let $\underline I$ be a level of the launch inventory at which always keeping production and sales on ($p=rI$, $s=d$) depletes the inventory exactly at $T$. Let $\overline I$ be a level at which always keeping production off and sales on ($p=0$, $s=d$) depletes the inventory exactly at $T$. All other parameters are the same in both. Then
--   $$\underline I<\overline I.$$
--
--   This is the inequality that makes the three cases of Theorem 1 ($I_L<\underline I$, $\underline I<I_L<\overline I$, $I_L>\overline I$) a partition of the launch inventories, up to the two boundary values.
--
--   **Formalization Note** The two levels are taken as real numbers together with their defining property (an admissible trajectory of the stated shape that depletes the inventory exactly at $T$).
-- source:
--   Hu & Sun, Managing self-replicating innovative goods, authors' manuscript of 2020-10-18 (Management Science, doi:10.1287/mnsc.2020.3936), p. 10, Theorem 1 (preamble: 'Clearly I̲ < Ī')

import Mathlib
import Definitions.Def_SelfReplic_Strong_Model

namespace SelfReplic.Strong

/-- Theorem 1 (preamble), p. 10: the level I̲ (production and sales always on deplete the
inventory exactly at `T`) is below the level Ī (production off, sales on deplete it exactly
at `T`). -/
theorem threshold_lt (P : Params) (hP : P.Standing) (hSR : P.StrongRepl)
    (Ilow Ihigh : ℝ)
    (hlow : IsLowLevel P Ilow) (hhigh : IsHighLevel P Ihigh) :
    Ilow < Ihigh := by sorry

end SelfReplic.Strong
