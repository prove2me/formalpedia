-- Prove2me | Theorems.Thm_RandPurIso_Completion_lemma_3_5
-- name    : RandPurIso.Completion.lemma_3_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:29:36.670237+00:00
-- url     : https://prove2.me/theorems/5a7dc524-4817-4391-bf60-4c794426fa11
-- title:
--   Lemma 3.5 — isometric equivalence of stateful oracles
-- statement:
--   Let $W_1:\mathsf{In}\otimes\mathsf{St}_1\to\mathsf{Out}\otimes\mathsf{St}_1$ and $W_2:\mathsf{In}\otimes\mathsf{St}_2\to\mathsf{Out}\otimes\mathsf{St}_2$ be contractions used as oracles with private initial states $|\varphi_1\rangle,|\varphi_2\rangle$. Suppose there is an isometry $J:\mathsf{St}_1\to\mathsf{St}_2$ with
--   $$J|\varphi_1\rangle=|\varphi_2\rangle\qquad\text{and}\qquad W_2(I_{\mathsf{In}}\otimes J)=(I_{\mathsf{Out}}\otimes J)W_1 .$$
--   Then every oracle algorithm $A$ satisfies $A^{\Phi^{W_1}}=A^{\Phi^{W_2}}$.
--
--   The lemma lets one change the private register of a stateful oracle by an isometry without changing what any algorithm sees; the paper uses it with $J=BC^{D^V}$ to pass from $W_3$ to $W_4$.
--
--   Differences from the source:
--   - reading: Φ^W for a stateful W adjoins |⊥⟩ to Out ⊗ St → |⊥⟩ embedded as |⊥⟩_Out ⊗ |φ⟩_St (contractionOracle); reason: Definition 3.2 needs the output in the form Out' ⊗ St; the paper does not say where ⊥ sits
--   - encoding: W1, W2 oracles with private initial states → W1, W2 contractions, φ1, φ2 unit vectors; reason: Φ^W is defined for contractions (Definition 3.4) and initial states are states
--   - generalization: A^O := A^O(|0⟩⟨0|_{Out,A}) on the workspace A (Definition 3.2) → any finite workspace W and any initial density matrix of the algorithm (OracleAlg.init); reason: Definition 3.2's "without loss of generality"; |0⟩⟨0| is the special case init = |0⟩⟨0|
-- source:
--   Goldin, On Random Purifications of Isometries and Channels, arXiv:2611.04573, Lemma 3.5, p. 18

import Mathlib
import Definitions.Def_RandPurIso_Completion_OracleAlg
import Definitions.Def_RandPurIso_Completion_contractionOracle
import Definitions.Def_RandPurIso_Completion_IsContraction
open Matrix

namespace RandPurIso.Completion

/-- **Lemma 3.5 (isometric equivalence of stateful oracles)** (Goldin, *On Random Purifications of Isometries and Channels*, arXiv:2611.04573, p. 18).

Let `W₁ : In ⊗ St₁ → Out ⊗ St₁`, `W₂ : In ⊗ St₂ → Out ⊗ St₂` be oracles with private initial states
`|φ₁⟩, |φ₂⟩`. Suppose there is an isometry `J : St₁ → St₂` with `J|φ₁⟩ = |φ₂⟩` and
`W₂(I_In ⊗ J) = (I_Out ⊗ J)W₁`. Then for every adaptive oracle algorithm `A`, `A^{Φ^{W₁}} = A^{Φ^{W₂}}`.

**Formalization Note.** `W₁, W₂` are contractions (they enter through `Φ`, Definition 3.4), and
`|φ₁⟩, |φ₂⟩` are unit vectors (states). `Φ^{W}` for a stateful `W` is `contractionOracle`. -/
theorem lemma_3_5 {In Out St1 St2 : Type} [Fintype In] [Fintype Out] [Fintype St1] [Fintype St2]
    [DecidableEq In] [DecidableEq Out] [DecidableEq St1] [DecidableEq St2]
    (W1 : Matrix (Out × St1) (In × St1) ℂ) (W2 : Matrix (Out × St2) (In × St2) ℂ)
    (φ1 : St1 → ℂ) (φ2 : St2 → ℂ) (J : Matrix St2 St1 ℂ)
    (hW1 : IsContraction W1) (hW2 : IsContraction W2)
    (hφ1 : ∑ s, ‖φ1 s‖ ^ 2 = 1) (hφ2 : ∑ s, ‖φ2 s‖ ^ 2 = 1)
    (hJ : Jᴴ * J = 1) (hJφ : J.mulVec φ1 = φ2)
    (hWJ : W2 * Matrix.kronecker (1 : Matrix In In ℂ) J =
      Matrix.kronecker (1 : Matrix Out Out ℂ) J * W1)
    (W : Type) [Fintype W] [DecidableEq W] (A : OracleAlg In (Option Out) W) :
    A.run (contractionOracle W1 φ1) = A.run (contractionOracle W2 φ2) := by sorry

end RandPurIso.Completion
