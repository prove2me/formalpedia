-- Prove2me | Theorems.Thm_ShorAdditivityEquiv_strongSuperadditive_imp_holevoAdditive
-- name    : ShorAdditivityEquiv.strongSuperadditive_imp_holevoAdditive
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T15:31:59.24854+00:00
-- url     : https://prove2.me/theorems/119c1098-57ba-40a1-83fa-fd59e2b413d5
-- title:
--   §8, p. 18 — (iv) ⇒ (ii): strong superadditivity of $E_F$ implies additivity of the Holevo capacity
-- statement:
--   If the entanglement of formation is strongly superadditive on every four-party system of every finite dimensions (statement (iv) of Theorem 1), then the Holevo capacity is additive for all pairs of channels of all finite dimensions (statement (ii)):
--   $$
--   \chi_{N_1\otimes N_2}=\chi_{N_1}+\chi_{N_2}.
--   $$
--   The paper attributes this implication to Matsumoto, Shimono and Winter and repeats the argument for completeness.
--
--   Differences from the source:
--   - reading: "That the additivity of χN follows [from strong superadditivity of EF] is known" → FormationStronglySuperadditive → HolevoCapacityAdditive (both global); reason: (i)–(iv) are conjectures about all channels / all states of all finite dimensions, and the proofs apply the hypothesis to auxiliary channels and states of other dimensions; a per-pair implication is a different (false) claim
--   - encoding: max / min over ensembles {p_i, |v_i⟩} or over vectors |φ⟩ (Eqs. (1)–(3), Theorem 1 (i)) → sSup / sInf over all finite pure-state ensembles of every size, or over all unit vectors; reason: on the domain of the statement (channels, density matrices, nonempty spaces) every set is nonempty and bounded (0 ≤ · ≤ log₂ d_out) and the extremum is attained (Carathéodory, compact unit sphere), so the values coincide
--   - encoding: spaces C^{d×d}, H_in, H_{A1}, … of finite dimension → nonempty finite types (Fintype, DecidableEq, Nonempty) in Type; reason: a 0-dimensional space carries no state, so Nonempty excludes no instance of the paper
--   - encoding: quantum channel (CPT map) → QAlgorithms.IsChannel (a finite Kraus family with Σ A_k†A_k = I); reason: the paper gives this operator-sum form as an equivalent characterization of finite-dimensional CPT maps (pp.2–3)
--   - encoding: vectors |φ⟩, |v_i⟩ of the input space → unit vectors (‖φ‖ = 1); reason: |φ⟩⟨φ| is meant as a state (p.4: "the minimization ranges over states |φ⟩"); ensemble members are states
--   - encoding: N1 ⊗ N2 → ShorEBAdditivity.tensorChannel N₁ N₂, defined on every operator by the matrix-unit expansion; reason: for linear maps it is the unique linear map with (N₁ ⊗ N₂)(X ⊗ Y) = N₁(X) ⊗ N₂(Y); it acts on entangled inputs too
-- source:
--   Shor, Equivalence of Additivity Questions in Quantum Information Theory, arXiv:quant-ph/0305035v4, §8, p. 18

import Mathlib
import Definitions.Def_ShorAdditivityEquiv_FormationStronglySuperadditive
import Definitions.Def_ShorAdditivityEquiv_HolevoCapacityAdditive

namespace ShorAdditivityEquiv

/-- Shor, *Equivalence of Additivity Questions in Quantum Information Theory*, arXiv:quant-ph/0305035v4, §8, p.18: (iv) ⇒ (ii). "All three additivity properties (i) to (iii) follow easily from
the assumption of strong superadditivity of EF. The additivity of EF follows trivially from this
assumption. That the additivity of χN follows is known [12]. We repeat this argument below for
completeness."

**Formalization Note.** Hypothesis and conclusion are the global propositions of Theorem 1
(`FormationStronglySuperadditive` and `HolevoCapacityAdditive`), each quantified over all finite dimensions and all channels or states.
The proof applies the hypothesis to auxiliary channels or states of other dimensions, so a
statement for one fixed pair of channels or states would be a different claim. -/
theorem strongSuperadditive_imp_holevoAdditive : FormationStronglySuperadditive → HolevoCapacityAdditive := by sorry

end ShorAdditivityEquiv
