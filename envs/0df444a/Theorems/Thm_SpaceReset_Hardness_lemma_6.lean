-- Prove2me | Theorems.Thm_SpaceReset_Hardness_lemma_6
-- name    : SpaceReset.Hardness.lemma_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T03:22:50.761192+00:00
-- url     : https://prove2.me/theorems/90bd2449-cd68-494a-8397-797648527d19
-- title:
--   Lemma 6 — global rank benchmark
-- statement:
--   Let $G\in\mathbb F_2^{k\times n}$ have full row rank, and let a Definition 4 implementation with memory budget $q$, discard budget $g$ and initial memory rank $r$ realize either output contract within error $\varepsilon$. Then
--   $$2^{q+g}\,r\ \ge\ (1-\varepsilon)\,2^k .$$
--   For $\varepsilon<1/2$ this gives $2q+g\ge k$ for any (mixed) initialization and $q+g\ge k$ for pure initialization.
--
--   This is the output-rank inequality behind the third term of the initial-rank frontier.
--
--   Differences from the source:
--   - encoding: Definition 4 online circuit: memory of dimension at most 2^q, fresh pure ancillas, a unitary and discarded systems of total dimension at most 2^g → DiscardDevice: one memory type M with |M| ≤ 2^q, a Stinespring isometry V_j : carrier⊗M → carrier⊗M⊗E_j per slot, and ∏_j |E_j| ≤ 2^g; reason: an isometry is exactly pure ancilla + unitary + discard; a memory of smaller dimension at some cut embeds isometrically into M with no extra discard; same class of realizations
--   - encoding: d_op = sup over adaptive testers with a quantum reference of the trace distance of final states (5); code state: trace distance of the joint returned state → ErrorLE: for every valid tester (one reference system R, initial state, a channel after each slot) the trace distance is ≤ ε; code state via the blank-input experiment that stores every returned carrier; reason: 'sup ≤ ε' is the same as 'every tester ≤ ε'; references of varying dimension embed into one R isometrically; the blank tester returns exactly the joint emitted state
-- source:
--   Rinka Miura, STOC 2027 submission #1715 (October 2026), Lemma 6, §2.2, p. 13

import Mathlib
import Definitions.Def_SpaceReset_Hardness_DiscardDevice

set_option autoImplicit false

namespace SpaceReset.Hardness

/-- Lemma 6 (Global rank benchmark), p. 13. -/
theorem lemma_6 {k n : ℕ} (G : Matrix (Fin k) (Fin n) F2) (hG : FullRowRank G)
    (q g : ℕ) (D : DiscardDevice n q g) (c : Contract) (ε : ℝ)
    (hD : ErrorLE G c D.toProcess ε) :
    (2 : ℝ) ^ (q + g) * (D.σ.rank : ℝ) ≥ (1 - ε) * (2 : ℝ) ^ k ∧
    (ε < 1 / 2 → k ≤ 2 * q + g) ∧
    (ε < 1 / 2 → D.PureInit → k ≤ q + g) := by sorry

end SpaceReset.Hardness
