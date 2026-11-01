-- Prove2me | Theorems.Thm_ShorAdditivityEquiv_holevoAdditive_imp_minOutputAdditive
-- name    : ShorAdditivityEquiv.holevoAdditive_imp_minOutputAdditive
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T15:32:21.759227+00:00
-- url     : https://prove2.me/theorems/7db4c5cd-4aac-477b-952a-ad7c5b6bcd86
-- title:
--   §9, pp. 18–19 — (ii) ⇒ (i): additivity of the Holevo capacity implies additivity of the minimum output entropy
-- statement:
--   If the Holevo capacity is additive for all pairs of channels of all finite dimensions (statement (ii) of Theorem 1), then the minimum output entropy is additive for all pairs of channels of all finite dimensions (statement (i)).
--
--   The argument applies the hypothesis not to the given channels $N_1$, $N_2$ but to the extended channels $N_1'(\rho\otimes|i\rangle\langle i|)=X_iN_1(\rho)X_i^\dagger$ built from generalized Pauli matrices, whose input spaces are larger; this is why the implication is between the global statements.
--
--   Differences from the source:
--   - reading: "Additivity of χN … implies additivity of min H(N)" → HolevoCapacityAdditive → MinOutputEntropyAdditive (both global); reason: (i)–(iv) are conjectures about all channels / all states of all finite dimensions, and the proofs apply the hypothesis to auxiliary channels and states of other dimensions; a per-pair implication is a different (false) claim
--   - encoding: max / min over ensembles {p_i, |v_i⟩} or over vectors |φ⟩ (Eqs. (1)–(3), Theorem 1 (i)) → sSup / sInf over all finite pure-state ensembles of every size, or over all unit vectors; reason: on the domain of the statement (channels, density matrices, nonempty spaces) every set is nonempty and bounded (0 ≤ · ≤ log₂ d_out) and the extremum is attained (Carathéodory, compact unit sphere), so the values coincide
--   - encoding: spaces C^{d×d}, H_in, H_{A1}, … of finite dimension → nonempty finite types (Fintype, DecidableEq, Nonempty) in Type; reason: a 0-dimensional space carries no state, so Nonempty excludes no instance of the paper
--   - encoding: quantum channel (CPT map) → QAlgorithms.IsChannel (a finite Kraus family with Σ A_k†A_k = I); reason: the paper gives this operator-sum form as an equivalent characterization of finite-dimensional CPT maps (pp.2–3)
--   - encoding: vectors |φ⟩, |v_i⟩ of the input space → unit vectors (‖φ‖ = 1); reason: |φ⟩⟨φ| is meant as a state (p.4: "the minimization ranges over states |φ⟩"); ensemble members are states
--   - encoding: N1 ⊗ N2 → ShorEBAdditivity.tensorChannel N₁ N₂, defined on every operator by the matrix-unit expansion; reason: for linear maps it is the unique linear map with (N₁ ⊗ N₂)(X ⊗ Y) = N₁(X) ⊗ N₂(Y); it acts on entangled inputs too
-- source:
--   Shor, Equivalence of Additivity Questions in Quantum Information Theory, arXiv:quant-ph/0305035v4, §9, pp. 18–19

import Mathlib
import Definitions.Def_ShorAdditivityEquiv_HolevoCapacityAdditive
import Definitions.Def_ShorAdditivityEquiv_MinOutputEntropyAdditive

namespace ShorAdditivityEquiv

/-- Shor, *Equivalence of Additivity Questions in Quantum Information Theory*, arXiv:quant-ph/0305035v4, §9, pp.18–19: (ii) ⇒ (i) (section title "Additivity of χN or of EF implies additivity of
min H(N)."). "Now, suppose there is some state |w⟩⟨w| which has smaller output entropy for the
channel N1 ⊗ N2 than H(N1(|v1⟩⟨v1|) + H(N2(|v2⟩⟨v2|)). We can use the ensemble containing states
|w⟩⟨w| ⊗ |i1, i2⟩⟨i1, i2|, for i1, i2 = 0 . . . d² − 1, with equal probabilities, to obtain a larger
capacity for the tensor product channel N′1 ⊗ N′2."

**Formalization Note.** Hypothesis and conclusion are the global propositions of Theorem 1
(`HolevoCapacityAdditive` and `MinOutputEntropyAdditive`), each quantified over all finite dimensions and all channels or states.
The proof applies the hypothesis to auxiliary channels or states of other dimensions, so a
statement for one fixed pair of channels or states would be a different claim. -/
theorem holevoAdditive_imp_minOutputAdditive : HolevoCapacityAdditive → MinOutputEntropyAdditive := by sorry

end ShorAdditivityEquiv
