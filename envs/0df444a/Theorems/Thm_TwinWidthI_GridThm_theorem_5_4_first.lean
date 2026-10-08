-- Prove2me | Theorems.Thm_TwinWidthI_GridThm_theorem_5_4_first
-- name    : TwinWidthI.GridThm.theorem_5_4_first
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T07:44:02.610832+00:00
-- url     : https://prove2.me/theorems/4866d0b4-3ca5-4a01-b9c9-113c914b568a
-- title:
--   Theorem 5.4, first item — every t-twin-ordered matrix is (2t+2)-mixed free
-- statement:
--   Let $M$ be an $n\times m$ matrix over a finite alphabet and $t\ge0$. If $M$ is $t$-twin-ordered — it has a division sequence (a contraction sequence in which every row and column partition consists of intervals) all of whose partitions have error value at most $t$ — then $M$ has no $(2t+2)$-mixed minor:
--
--   $$M\ \text{$t$-twin-ordered}\ \Longrightarrow\ M\ \text{is }(2t+2)\text{-mixed free}.$$
--
--   This is the "only if" direction of the Grid Minor Theorem: bounded twin-width, in the right order, excludes large mixed minors.
--
--   **Formalization Note** The page writes "2t + 2-mixed free", meaning $(2t+2)$-mixed free. No hypothesis is added.
-- source:
--   Bonnet, Kim, Thomassé and Watrigant, Twin-width I: Tractable FO Model Checking, J. ACM 69(1), Article 3 (2021), p. 3:19, Theorem 5.4 (first item), proved on pp. 3:21–3:22

import Mathlib
import Definitions.Def_TwinWidthI_GridThm_Setting

namespace TwinWidthI.GridThm

/-- Theorem 5.4, first item (proved on pp. 3:21–3:22): every `t`-twin-ordered matrix is
`(2t + 2)`-mixed free. -/
theorem theorem_5_4_first {A : Type*} [Fintype A] {n m : ℕ} (M : Matrix (Fin n) (Fin m) A) (t : ℕ)
    (h : TwinOrdered M t) : MixedFree M (2 * t + 2) := by sorry

end TwinWidthI.GridThm
