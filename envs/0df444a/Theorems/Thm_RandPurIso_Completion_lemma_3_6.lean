-- Prove2me | Theorems.Thm_RandPurIso_Completion_lemma_3_6
-- name    : RandPurIso.Completion.lemma_3_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:30:06.181617+00:00
-- url     : https://prove2.me/theorems/63c415a6-aaff-41db-9c38-db91ecd96b6a
-- title:
--   Lemma 3.6 — operator-norm closeness gives $\mathrm{TD}\le 2t\epsilon$
-- statement:
--   Let $V_1,V_2:\mathsf{In}\otimes\mathsf{St}\to\mathsf{Out}\otimes\mathsf{St}$ be contractions, used as oracles with the same private initial state $|\varphi\rangle$, such that
--   $$\|V_1-V_2\|_{op}\le\epsilon .$$
--   Then for every oracle algorithm $A$ making $t$ queries,
--   $$\mathrm{TD}\big(A^{\Phi^{V_1}},A^{\Phi^{V_2}}\big)\le 2t\epsilon .$$
--
--   This converts operator-norm estimates on the hybrid oracles of Theorem 5.4 into trace-distance bounds on algorithm outputs.
--
--   Differences from the source:
--   - generalization: two contractions V1, V2 (stateless) → stateful V1, V2 : In ⊗ St → Out ⊗ St with a common unit initial state; reason: the paper applies it to stateful hybrids (p. 33); St = Unit gives the stated case
--   - reading: Φ^V for a stateful V adjoins |⊥⟩ to Out ⊗ St → |⊥⟩ embedded as |⊥⟩_Out ⊗ |φ⟩_St (contractionOracle); reason: Definition 3.2 needs the output in the form Out' ⊗ St
--   - generalization: A^O := A^O(|0⟩⟨0|_{Out,A}) on the workspace A (Definition 3.2) → any finite workspace W and any initial density matrix of the algorithm (OracleAlg.init); reason: Definition 3.2's "without loss of generality"; |0⟩⟨0| is the special case init = |0⟩⟨0|
-- source:
--   Goldin, On Random Purifications of Isometries and Channels, arXiv:2611.04573, Lemma 3.6, p. 19

import Mathlib
import Definitions.Def_RandPurIso_Completion_OracleAlg
import Definitions.Def_RandPurIso_Completion_contractionOracle
import Definitions.Def_RandPurIso_Completion_IsContraction
import Definitions.Def_RandPurIso_Completion_opNorm
import Definitions.Def_RandPurIso_Completion_traceDist
open Matrix

namespace RandPurIso.Completion

/-- **Lemma 3.6** (Goldin, *On Random Purifications of Isometries and Channels*, arXiv:2611.04573, p. 19). Let `V₁, V₂` be two contractions with `‖V₁ − V₂‖_op ≤ ε`.
Then for any `t`-query oracle algorithm `A`, `TD(A^{Φ^{V₁}}, A^{Φ^{V₂}}) ≤ 2tε`.

**Formalization Note.** `V₁, V₂` may be stateful, `In ⊗ St → Out ⊗ St` with a common initial state
`|φ⟩` (as in its use on p. 33); `St = Unit` is the stateless case. `t` is the number of queries of `A`. -/
theorem lemma_3_6 {In Out St : Type} [Fintype In] [Fintype Out] [Fintype St]
    [DecidableEq In] [DecidableEq Out] [DecidableEq St]
    (V1 V2 : Matrix (Out × St) (In × St) ℂ) (φ : St → ℂ) (ε : ℝ)
    (hV1 : IsContraction V1) (hV2 : IsContraction V2) (hφ : ∑ s, ‖φ s‖ ^ 2 = 1)
    (hε : opNorm (V1 - V2) ≤ ε) (W : Type) [Fintype W] [DecidableEq W]
    (A : OracleAlg In (Option Out) W) :
    traceDist (A.run (contractionOracle V1 φ)) (A.run (contractionOracle V2 φ)) ≤
      2 * A.numQueries * ε := by sorry

end RandPurIso.Completion
