-- Prove2me | Theorems.Thm_RandPurIso_Completion_theorem_3_17
-- name    : RandPurIso.Completion.theorem_3_17
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:29:44.088632+00:00
-- url     : https://prove2.me/theorems/a243d723-e60e-46cf-833c-e8ff1dc4ee82
-- title:
--   Theorem 3.17 — purified oracles
-- statement:
--   Let $A=\{a_1,\dots,a_\ell\}$ be a finite set, $t\ge1$, $\mathsf{St}=\mathcal H(\mathbb Z_t)^{\otimes\ell}$ and $PO$ the purified oracle that increases the $i$-th register by $1$ (mod $t$) on input $a_i$, with initial state $|0,\dots,0\rangle$. Then for every oracle algorithm $A$,
--   $$\mathop{\mathbb E}_{f:A\to[t]}\big[A^{S^f}\big]=A^{PO},$$
--   the expectation being the uniform average over the $t^\ell$ functions. Query access to $PO$ is identical to query access to the phase oracle of a uniformly random function; Theorem 4.1 uses the case $A=\{0,1\}$.
--
--   Differences from the source:
--   - encoding: t ∈ ℕ, Z_t → t ≥ 1 (NeZero t); St has basis A → Fin t; reason: Z_0 is empty and there is no function A → [0]; only excludes an undefined case
--   - generalization: A^O := A^O(|0⟩⟨0|_{Out,A}) on the workspace A (Definition 3.2) → any finite workspace W and any initial density matrix of the algorithm (OracleAlg.init); reason: Definition 3.2's "without loss of generality"; |0⟩⟨0| is the special case init = |0⟩⟨0|
-- source:
--   Goldin, On Random Purifications of Isometries and Channels, arXiv:2611.04573, Theorem 3.17, pp. 24–25

import Mathlib
import Definitions.Def_RandPurIso_Completion_OracleAlg
import Definitions.Def_RandPurIso_Completion_contractionOracle
import Definitions.Def_RandPurIso_Completion_phaseOracleMat
import Definitions.Def_RandPurIso_Completion_purifiedOracleMat
open Matrix

namespace RandPurIso.Completion

/-- **Theorem 3.17 (generalized purified oracles, [Zha19, AG26])** (Goldin, *On Random Purifications of Isometries and Channels*, arXiv:2611.04573, pp. 24–25).

Let `A = {a₁, …, a_ℓ}`, `t ∈ ℕ`, `St = H(Z_t)^{⊗ℓ}` and `PO|a_i⟩|c⟩ = |a_i⟩|c + e_i⟩` (mod `t`), with
initial state `|{0, …, 0}⟩`. Then for every oracle algorithm `A`,
`E_{f : A → [t]} [A^{S^f}] = A^{PO}`.

**Formalization Note.** `E_f` is the uniform average over the `t^ℓ` functions. Both oracles are
used through `Φ` (Definition 3.4), as the paper's notation `A^V := A^{Φ_V}`; both are unitary, so no
`⊥` occurs. `t ≥ 1` (`NeZero t`): `Z_0` is empty and `[0]` has no functions. -/
theorem theorem_3_17 (A : Type) [Fintype A] [DecidableEq A] (t : ℕ) [NeZero t]
    (W : Type) [Fintype W] [DecidableEq W] (Alg : OracleAlg A (Option A) W) :
    ((t : ℂ) ^ Fintype.card A)⁻¹ •
        ∑ f : A → Fin t, Alg.run (contractionOracle (liftUnit (phaseOracleMat t f)) unitInit) =
      Alg.run (contractionOracle (purifiedOracleMat A t) (purifiedInit A t)) := by sorry

end RandPurIso.Completion
