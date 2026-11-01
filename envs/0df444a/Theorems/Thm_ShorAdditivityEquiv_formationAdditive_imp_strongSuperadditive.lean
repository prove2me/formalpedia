-- Prove2me | Theorems.Thm_ShorAdditivityEquiv_formationAdditive_imp_strongSuperadditive
-- name    : ShorAdditivityEquiv.formationAdditive_imp_strongSuperadditive
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T15:30:33.239989+00:00
-- url     : https://prove2.me/theorems/f97e0616-e795-4f9e-b579-064d92144f66
-- title:
--   §6, pp. 12–15 — (iii) ⇒ (iv): additivity of $E_F$ implies strong superadditivity of $E_F$
-- statement:
--   If the entanglement of formation is additive for all pairs of bipartite states of all finite dimensions (statement (iii) of Theorem 1), then it is strongly superadditive: for every density matrix $\sigma$ on every four-party system $\mathcal H_{A_1}\otimes\mathcal H_{A_2}\otimes\mathcal H_{B_1}\otimes\mathcal H_{B_2}$,
--   $$
--   E_F(\sigma)\ge E_F(\mathrm{Tr}_2\,\sigma)+E_F(\mathrm{Tr}_1\,\sigma)
--   $$
--   (statement (iv)). This is the hardest implication of the paper.
--
--   Differences from the source:
--   - reading: "additivity of entanglement of formation implies strong superadditivity of entanglement of formation" → FormationAdditive → FormationStronglySuperadditive (both global); reason: (i)–(iv) are conjectures about all channels / all states of all finite dimensions, and the proofs apply the hypothesis to auxiliary channels and states of other dimensions; a per-pair implication is a different (false) claim
--   - encoding: max / min over ensembles {p_i, |v_i⟩} or over vectors |φ⟩ (Eqs. (1)–(3), Theorem 1 (i)) → sSup / sInf over all finite pure-state ensembles of every size, or over all unit vectors; reason: on the domain of the statement (channels, density matrices, nonempty spaces) every set is nonempty and bounded (0 ≤ · ≤ log₂ d_out) and the extremum is attained (Carathéodory, compact unit sphere), so the values coincide
--   - encoding: spaces C^{d×d}, H_in, H_{A1}, … of finite dimension → nonempty finite types (Fintype, DecidableEq, Nonempty) in Type; reason: a 0-dimensional space carries no state, so Nonempty excludes no instance of the paper
--   - encoding: σ1 ⊗ σ2 with E_F "calculated over the bipartite A–B partition" → tensorState σ₁ σ₂ on (A₁ × A₂) × (B₁ × B₂), the Kronecker product regrouped to the cut A₁A₂ | B₁B₂; reason: this is the paper's cut; formation traces the second factor
-- source:
--   Shor, Equivalence of Additivity Questions in Quantum Information Theory, arXiv:quant-ph/0305035v4, §6, pp. 12–15

import Mathlib
import Definitions.Def_ShorAdditivityEquiv_FormationAdditive
import Definitions.Def_ShorAdditivityEquiv_FormationStronglySuperadditive

namespace ShorAdditivityEquiv

/-- Shor, *Equivalence of Additivity Questions in Quantum Information Theory*, arXiv:quant-ph/0305035v4, §6, pp.12–15: (iii) ⇒ (iv). "In this section, we will show that additivity of
entanglement of formation implies strong superadditivity of entanglement of formation."

**Formalization Note.** Hypothesis and conclusion are the global propositions of Theorem 1
(`FormationAdditive` and `FormationStronglySuperadditive`), each quantified over all finite dimensions and all channels or states.
The proof applies the hypothesis to auxiliary channels or states of other dimensions, so a
statement for one fixed pair of channels or states would be a different claim. -/
theorem formationAdditive_imp_strongSuperadditive : FormationAdditive → FormationStronglySuperadditive := by sorry

end ShorAdditivityEquiv
