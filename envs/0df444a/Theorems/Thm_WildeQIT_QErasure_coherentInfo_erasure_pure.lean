-- Prove2me | Theorems.Thm_WildeQIT_QErasure_coherentInfo_erasure_pure
-- name    : WildeQIT.QErasure.coherentInfo_erasure_pure
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T18:38:03.668441+00:00
-- url     : https://prove2.me/theorems/86d20bb5-c394-401f-bf92-b771ed340219
-- title:
--   Eqs. (24.122)–(24.130): $I(A\rangle B)_\sigma=(1-2\varepsilon)H(A)_\varphi$ for the erasure channel
-- statement:
--   Let $\mathcal N$ be the quantum erasure channel with erasure probability $\varepsilon$, and let $\varphi_{AA'}$ be any pure bipartite input state. Sending the $A'$ share through the channel produces
--
--   $$
--   \sigma_{AB}\equiv(1-\varepsilon)\,\varphi_{AB}+\varepsilon\,\varphi_A\otimes|e\rangle\langle e|_B ,
--   $$
--
--   and its coherent information is
--
--   $$
--   I(A\rangle B)_\sigma=(1-2\varepsilon)\,H(A)_\varphi .
--   $$
--
--   This identity reduces the coherent information of the erasure channel to the entanglement entropy of the input.
--
--   **Formalization Note** $\sigma_{AB}=(\mathrm{id}_A\otimes\mathcal N)(|\varphi\rangle\langle\varphi|)$ through `QAlgorithms.idTensorSuperop`; $\varphi_A=\mathrm{Tr}_{A'}\varphi_{AA'}$ is `WildeQIT.partialTraceRight`; $H$ is `QAlgorithms.vnEntropy` in bits.
--
--   Differences from the source:
--   - generalization: the computation is carried out for ε ∈ [0, 1/2] → ε ∈ [0, 1]; reason: the derivation (24.126)–(24.130) does not use ε ≤ 1/2; the Lean statement specializes to the book’s range
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, proof of Proposition 24.7.1, (24.122), p. 677, and (24.126)–(24.130), p. 678

import Definitions.Def_WildeQIT_Degradable_coherentInfoState
import Definitions.Def_WildeQIT_Degradable_PureInput
import Definitions.Def_WildeQIT_QErasure_erasureChannel
import Definitions.Def_QAlgorithms_Defs_Channel

/-!
Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8, proof of Proposition 24.7.1,
pp. 677–678, eqs. (24.122) and (24.126)–(24.130).
-/

namespace WildeQIT.QErasure

/-- **Eqs. (24.122), (24.126)–(24.130)** (Wilde, *From Classical to Quantum Shannon Theory*,
arXiv:1106.1445v8, pp. 677–678): sending one share of a pure bipartite state `φ_{AA′}` through the
quantum erasure channel produces `σ_{AB} ≡ (1 − ε) φ_{AB} + ε φ_A ⊗ |e⟩⟨e|_B` (24.122), and its
coherent information is `I(A⟩B)_σ = (1 − 2ε) H(A)_φ` (24.130).

**Formalization Note.** `φ_{AA′}` is any unit vector on `Fin m × a` with a reference `A = Fin m` of
any dimension (`PureInput`); `σ_{AB}` is `(id_A ⊗ N)(|φ⟩⟨φ|)` through the published
`QAlgorithms.idTensorSuperop`; `φ_A = Tr_{A′} φ_{AA′}` is the published `WildeQIT.partialTraceRight`;
`H` is the published von Neumann entropy `QAlgorithms.vnEntropy` (bits). The identity is stated for
every `ε ∈ [0, 1]`, which is the range on which the book's derivation (24.126)–(24.130) holds. -/
theorem coherentInfo_erasure_pure (a : Type) [Fintype a] [DecidableEq a] (ε : ℝ) (h0 : 0 ≤ ε)
    (h1 : ε ≤ 1) (φ : WildeQIT.Degradable.PureInput a) :
    WildeQIT.Degradable.coherentInfoState (QAlgorithms.idTensorSuperop (R := Fin φ.m) (erasureChannel a ε h0 h1).apply
        (QAlgorithms.pureDensity φ.ψ)) =
      (1 - 2 * ε) * QAlgorithms.vnEntropy (partialTraceRight (QAlgorithms.pureDensity φ.ψ)) := by sorry

end WildeQIT.QErasure
