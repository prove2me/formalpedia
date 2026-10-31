-- Prove2me | Theorems.Thm_PandoraComb_proposition_4_2
-- name    : PandoraComb.proposition_4_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:11:57.923199+00:00
-- url     : https://prove2.me/theorems/02e6b845-d9c0-4dad-ad0c-2876e7af1b6c
-- title:
--   Proposition 4.2 — the lifted cost $c'(S)=c(\{i\mid\exists j,(i,j)\in S\})$ is submodular when $c$ is
-- statement:
--   Let $c$ be a submodular set function on the boxes, and for sets $S$ of pairs $(i,j)$ let
--   $$c'(S)=c\big(\{i\mid\exists j:\ (i,j)\in S\}\big).$$
--   If $c$ is submodular, i.e. $c(x\mid B)\le c(x\mid A)$ for all $A\subseteq B$ and $x\notin B$, then $c'$ is submodular.
--
--   Transformation $T$ therefore maps instances with submodular cost to Bernoulli instances with submodular cost, to which Theorem 3.1 applies.
--
--   Differences from the source:
--   - generalization: c : 2^[n] → ℝ≥0, copies indexed by j ∈ [m] → any c : Finset ι → ℝ and copies indexed by any type κ with decidable equality; reason: the proof uses neither the sign of c nor finiteness of the copy index; the paper's case is an instance
-- source:
--   Berger, Ezra, Feldman & Fusco, Pandora’s Problem with Combinatorial Cost, arXiv:2303.01078v1, Proposition 4.2, p.19 (Transformation 2, p.19)

import Definitions.Def_PandoraComb_Bernoullify
import Definitions.Def_SubsamplingSM_Offline_IsSubmodular

namespace PandoraComb

/-- **Proposition 4.2** (arXiv:2303.01078v1, p.19): "If c is submodular, then c′ obtained by
transformation T is also submodular."

**Formalization Note.** `c′ = liftCost c`, `c′(S) = c({i | ∃ j, (i, j) ∈ S})` (p.19). The copy
index `j` ranges over any type `κ` (the paper's `[m]`), and `c` may take any real values. -/
theorem proposition_4_2 {ι κ : Type*} [DecidableEq ι] [DecidableEq κ] (c : Finset ι → ℝ)
    (hsub : SubsamplingSM.Offline.IsSubmodular c) :
    SubsamplingSM.Offline.IsSubmodular (liftCost (κ := κ) c) := by sorry

end PandoraComb
