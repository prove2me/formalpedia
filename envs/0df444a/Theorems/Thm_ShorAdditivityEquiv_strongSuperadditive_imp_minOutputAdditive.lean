-- Prove2me | Theorems.Thm_ShorAdditivityEquiv_strongSuperadditive_imp_minOutputAdditive
-- name    : ShorAdditivityEquiv.strongSuperadditive_imp_minOutputAdditive
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T15:30:43.01925+00:00
-- url     : https://prove2.me/theorems/2881fbc6-5119-406d-b978-eb8be506edcc
-- title:
--   §8, p. 18 — (iv) ⇒ (i): strong superadditivity of $E_F$ implies additivity of the minimum output entropy
-- statement:
--   If the entanglement of formation is strongly superadditive on every four-party system of every finite dimensions (statement (iv) of Theorem 1), then the minimum output entropy is additive for all pairs of channels of all finite dimensions (statement (i)):
--   $$
--   \min_{|\phi\rangle} H\big((N_1\otimes N_2)(|\phi\rangle\langle\phi|)\big)=\min_{|\phi\rangle} H\big(N_1(|\phi\rangle\langle\phi|)\big)+\min_{|\phi\rangle} H\big(N_2(|\phi\rangle\langle\phi|)\big).
--   $$
--   The paper notes that this implication was not in the literature before.
--
--   Differences from the source:
--   - reading: "strong superadditivity of EF implies additivity of minimum output entropy" → FormationStronglySuperadditive → MinOutputEntropyAdditive (both global); reason: (i)–(iv) are conjectures about all channels / all states of all finite dimensions, and the proofs apply the hypothesis to auxiliary channels and states of other dimensions; a per-pair implication is a different (false) claim
--   - encoding: max / min over ensembles {p_i, |v_i⟩} or over vectors |φ⟩ (Eqs. (1)–(3), Theorem 1 (i)) → sSup / sInf over all finite pure-state ensembles of every size, or over all unit vectors; reason: on the domain of the statement (channels, density matrices, nonempty spaces) every set is nonempty and bounded (0 ≤ · ≤ log₂ d_out) and the extremum is attained (Carathéodory, compact unit sphere), so the values coincide
--   - encoding: spaces C^{d×d}, H_in, H_{A1}, … of finite dimension → nonempty finite types (Fintype, DecidableEq, Nonempty) in Type; reason: a 0-dimensional space carries no state, so Nonempty excludes no instance of the paper
--   - encoding: quantum channel (CPT map) → QAlgorithms.IsChannel (a finite Kraus family with Σ A_k†A_k = I); reason: the paper gives this operator-sum form as an equivalent characterization of finite-dimensional CPT maps (pp.2–3)
--   - encoding: vectors |φ⟩, |v_i⟩ of the input space → unit vectors (‖φ‖ = 1); reason: |φ⟩⟨φ| is meant as a state (p.4: "the minimization ranges over states |φ⟩"); ensemble members are states
--   - encoding: N1 ⊗ N2 → ShorEBAdditivity.tensorChannel N₁ N₂, defined on every operator by the matrix-unit expansion; reason: for linear maps it is the unique linear map with (N₁ ⊗ N₂)(X ⊗ Y) = N₁(X) ⊗ N₂(Y); it acts on entangled inputs too
-- source:
--   Shor, Equivalence of Additivity Questions in Quantum Information Theory, arXiv:quant-ph/0305035v4, §8, p. 18

import Mathlib
import Definitions.Def_ShorAdditivityEquiv_FormationStronglySuperadditive
import Definitions.Def_ShorAdditivityEquiv_MinOutputEntropyAdditive

namespace ShorAdditivityEquiv

/-- Shor, *Equivalence of Additivity Questions in Quantum Information Theory*, arXiv:quant-ph/0305035v4, §8, p.18: (iv) ⇒ (i). "Finally, the proof that strong superadditivity of EF implies
additivity of minimum output entropy is equally easy, although I am not aware of its being in
the literature."

**Formalization Note.** Hypothesis and conclusion are the global propositions of Theorem 1
(`FormationStronglySuperadditive` and `MinOutputEntropyAdditive`), each quantified over all finite dimensions and all channels or states.
The proof applies the hypothesis to auxiliary channels or states of other dimensions, so a
statement for one fixed pair of channels or states would be a different claim. -/
theorem strongSuperadditive_imp_minOutputAdditive : FormationStronglySuperadditive → MinOutputEntropyAdditive := by sorry

end ShorAdditivityEquiv
