-- Prove2me | Theorems.Thm_SmallBiasPRF_lemma_17
-- name    : SmallBiasPRF.lemma_17
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T09:11:24.087044+00:00
-- url     : https://prove2.me/theorems/99da16f9-9e07-48d3-91c4-3a329488c6f3
-- title:
--   Lemma 17 — $|\Lambda_B(S)|$ is $1$ or $1/3$ according to the count parities
-- statement:
--   Let $B$ be nonempty and $S:B\to\mathbb F_3$. If
--
--   $$C_{B,0}(S)\bmod 2=C_{B,1}(S)\bmod 2=C_{B,2}(S)\bmod 2,\tag{14}$$
--
--   then $|\Lambda_B(S)|=1$; otherwise $|\Lambda_B(S)|=1/3$.
--
--   Thus a contracting state shrinks the squared weight $\Lambda_B^2$ by the factor $1/9$; Lemma 29 uses both values.
--
--   Differences from the source:
--   - generalization: B ⊆ A ⊆ {0,1}ⁿ nonempty → B any nonempty Finset of an arbitrary type α, S : α → ZMod 3 read on B; reason: Λ_B and C_{B,r} depend only on the values S(a), a ∈ B; the paper's B is a special case
-- source:
--   Dinur–Ishai, Towards Asymptotically Optimal Pseudorandom Functions: Linear-Size Circuits with Exponentially Small Bias, STOC 2027 submission (version of 2026-11-03, sha256 65dbd47e…), Lemma 17, p.24 (PDF 27)

import Mathlib
import Definitions.Def_SmallBiasPRF_Lambda

namespace SmallBiasPRF

/-- **Lemma 17** (contraction values), p.24 (PDF p.27).
Dinur–Ishai, *Towards Asymptotically Optimal Pseudorandom Functions: Linear-Size Circuits with
Exponentially Small Bias*, STOC 2027 submission (version of 2026-11-03, sha256 65dbd47e…), Lemma 17, p.24 (PDF p.27).

Let `B` be nonempty and `S : B → 𝔽₃`. If `C_{B,0}(S) mod 2 = C_{B,1}(S) mod 2 = C_{B,2}(S) mod 2`
(condition (14)), then `|Λ_B(S)| = 1`. Otherwise `|Λ_B(S)| = 1/3`.

**Formalization Note.** `B` is a nonempty finite subset of an arbitrary type `α` (in the paper
`B ⊆ A ⊆ {0,1}ⁿ`); `Λ_B` and `C_{B,r}` depend only on the values `S(a)`, `a ∈ B`, of a total
function `S : α → ZMod 3`. -/
theorem lemma_17 {α : Type*} (B : Finset α) (hB : B.Nonempty) (S : α → ZMod 3) :
    (IsNoncontracting B S → |Lambda B S| = 1) ∧
      (¬ IsNoncontracting B S → |Lambda B S| = 1 / 3) := by sorry

end SmallBiasPRF
