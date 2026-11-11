-- Prove2me | Theorems.Thm_SeedRecyclingDL_Codes_lemma_C_6
-- name    : SeedRecyclingDL.Codes.lemma_C_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:09:20.005205+00:00
-- url     : https://prove2.me/theorems/794b5534-e063-474c-9b8c-bf2485969260
-- title:
--   Lemma C.6 — Enumerating DL balls
-- statement:
--   For every finite binary word $u$ of length $\ell$ and every nonnegative integer $q$, the actual operation-tree traversal lists exactly $B_q(u)$, with repetitions allowed. It has at most
--   $$M(\ell,q)=(q+1)(5(\ell+q)+2)^q$$
--   entries. One fixed deterministic bit program produces that list within $C M(\ell,q)(\ell+q+1)$ bit operations, with a uniform constant $C>0$ chosen before $q$ and $u$. The zero-step endpoint is included. This supplies competitor, suffix-neighborhood, and preimage lists by filtering; no output-sensitivity assumption is made.
--
--   Differences from the source:
--   - encoding: binary strings and one-based positions → lists of Fin 2 with length predicates and current-word zero-based positions; reason: the order-preserving representation includes empty intermediate words and every unrestricted DL script
--   - encoding: asymptotic deterministic bit complexity → finite programs with actual charged RAM executions and uniform positive constants before lengths and inputs; reason: the fixed instruction semantics generates costs; a function with an assigned runtime is not accepted
--   - reading: bit operations on a RAM without a prescribed tape layout → helper routines use length and packed-value natural cells, while main and generic decoders receive raw bit streams; reason: each cell read and output is charged by bit length; raw decoder streams permit bounded inspection of arbitrarily long invalid inputs
-- source:
--   Quan D. Bui, Manabu Hagiwara, Shuche Wang, Van Khu Vu, STOC 2027 submission #1449 (October 2026), Lemma C.6, printed p. 20 (PDF p. 22); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1449.pdf

import Definitions.Def_SeedRecyclingDL_Codes_FieldExecution

set_option autoImplicit false

namespace SeedRecyclingDL.Codes

theorem lemma_C_6 :
    ∃ (enumerator : Program) (C : ℝ), 0 < C ∧
      ∀ (q : ℕ) (u : Word),
        (∀ v : Word, v ∈ enumerateBall q u ↔ v ∈ ball q u) ∧
        (enumerateBall q u).length ≤ ballListBound u.length q ∧
        Executes enumerator u.length [q, value u]
          (some (packedWords (enumerateBall q u)))
          (C * (ballListBound u.length q : ℕ) * (u.length + q + 1 : ℕ)) := by sorry

end SeedRecyclingDL.Codes
