-- Prove2me | Theorems.Thm_ShorAdditivityEquiv_minOutputAdditive_imp_formationAdditive
-- name    : ShorAdditivityEquiv.minOutputAdditive_imp_formationAdditive
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T15:31:43.34324+00:00
-- url     : https://prove2.me/theorems/b31cb438-8e3e-4a97-96c4-64a406128f25
-- title:
--   §7, pp. 15–17 — (i) ⇒ (iii): additivity of the minimum output entropy implies additivity of $E_F$
-- statement:
--   If the minimum output entropy is additive for all pairs of channels of all finite dimensions (statement (i) of Theorem 1), then the entanglement of formation is additive for all pairs of bipartite states of all finite dimensions (statement (iii)):
--   $$
--   E_F(\sigma_1\otimes\sigma_2)=E_F(\sigma_1)+E_F(\sigma_2).
--   $$
--
--   Differences from the source:
--   - reading: "Additivity of min H(N) implies additivity of EF" → MinOutputEntropyAdditive → FormationAdditive (both global); reason: (i)–(iv) are conjectures about all channels / all states of all finite dimensions, and the proofs apply the hypothesis to auxiliary channels and states of other dimensions; a per-pair implication is a different (false) claim
--   - encoding: max / min over ensembles {p_i, |v_i⟩} or over vectors |φ⟩ (Eqs. (1)–(3), Theorem 1 (i)) → sSup / sInf over all finite pure-state ensembles of every size, or over all unit vectors; reason: on the domain of the statement (channels, density matrices, nonempty spaces) every set is nonempty and bounded (0 ≤ · ≤ log₂ d_out) and the extremum is attained (Carathéodory, compact unit sphere), so the values coincide
--   - encoding: spaces C^{d×d}, H_in, H_{A1}, … of finite dimension → nonempty finite types (Fintype, DecidableEq, Nonempty) in Type; reason: a 0-dimensional space carries no state, so Nonempty excludes no instance of the paper
--   - encoding: quantum channel (CPT map) → QAlgorithms.IsChannel (a finite Kraus family with Σ A_k†A_k = I); reason: the paper gives this operator-sum form as an equivalent characterization of finite-dimensional CPT maps (pp.2–3)
--   - encoding: vectors |φ⟩, |v_i⟩ of the input space → unit vectors (‖φ‖ = 1); reason: |φ⟩⟨φ| is meant as a state (p.4: "the minimization ranges over states |φ⟩"); ensemble members are states
--   - encoding: σ1 ⊗ σ2 with E_F "calculated over the bipartite A–B partition" → tensorState σ₁ σ₂ on (A₁ × A₂) × (B₁ × B₂), the Kronecker product regrouped to the cut A₁A₂ | B₁B₂; reason: this is the paper's cut; formation traces the second factor
--   - encoding: N1 ⊗ N2 → ShorEBAdditivity.tensorChannel N₁ N₂, defined on every operator by the matrix-unit expansion; reason: for linear maps it is the unique linear map with (N₁ ⊗ N₂)(X ⊗ Y) = N₁(X) ⊗ N₂(Y); it acts on entangled inputs too
-- source:
--   Shor, Equivalence of Additivity Questions in Quantum Information Theory, arXiv:quant-ph/0305035v4, §7, pp. 15–17

import Mathlib
import Definitions.Def_ShorAdditivityEquiv_MinOutputEntropyAdditive
import Definitions.Def_ShorAdditivityEquiv_FormationAdditive

namespace ShorAdditivityEquiv

/-- Shor, *Equivalence of Additivity Questions in Quantum Information Theory*, arXiv:quant-ph/0305035v4, §7, pp.15–17: (i) ⇒ (iii) (section title "Additivity of min H(N) implies additivity of
EF."). "Letting q go to 1, we have subadditivity of the constrained Holevo capacity, implying
additivity of the entanglement of formation."

**Formalization Note.** Hypothesis and conclusion are the global propositions of Theorem 1
(`MinOutputEntropyAdditive` and `FormationAdditive`), each quantified over all finite dimensions and all channels or states.
The proof applies the hypothesis to auxiliary channels or states of other dimensions, so a
statement for one fixed pair of channels or states would be a different claim. -/
theorem minOutputAdditive_imp_formationAdditive : MinOutputEntropyAdditive → FormationAdditive := by sorry

end ShorAdditivityEquiv
