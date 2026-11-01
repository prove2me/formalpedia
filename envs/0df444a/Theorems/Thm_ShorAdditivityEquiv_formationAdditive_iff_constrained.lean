-- Prove2me | Theorems.Thm_ShorAdditivityEquiv_formationAdditive_iff_constrained
-- name    : ShorAdditivityEquiv.formationAdditive_iff_constrained
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T15:32:34.35317+00:00
-- url     : https://prove2.me/theorems/38d46d9b-b2fa-499b-8bd4-791e5a605d1b
-- title:
--   §3, p. 7 — additivity of $E_F$ is equivalent to additivity of the constrained capacity $\chi_N(\rho)$
-- statement:
--   The following two global statements are equivalent:
--
--   1. the entanglement of formation is additive: $E_F(\sigma_1\otimes\sigma_2)=E_F(\sigma_1)+E_F(\sigma_2)$ for all bipartite states $\sigma_1$, $\sigma_2$ of all finite dimensions (statement (iii) of Theorem 1);
--   2. the constrained Holevo capacity is additive: for all channels $N_1$, $N_2$ and all input density matrices $\rho_1$, $\rho_2$ of all finite dimensions,
--   $$
--   \chi_{N_1\otimes N_2}(\rho_1\otimes\rho_2) = \chi_{N_1}(\rho_1)+\chi_{N_2}(\rho_2).
--   $$
--
--   This is the paper's remark "the entanglement of formation $E_F$ is additive if and only if the constrained capacity $\chi_N(\rho)$ is", obtained from the MSW correspondence and the additivity of the entropy of product outputs.
--
--   Differences from the source:
--   - reading: "E_F is additive if and only if the constrained capacity χN(ρ) is" → FormationAdditive ↔ ConstrainedHolevoAdditive, both quantified over all finite dimensions, all states / all channels and input states; reason: (i)–(iv) are conjectures about all channels / all states of all finite dimensions, and the proofs apply the hypothesis to auxiliary channels and states of other dimensions; a per-pair implication is a different (false) claim
--   - encoding: max / min over ensembles {p_i, |v_i⟩} or over vectors |φ⟩ (Eqs. (1)–(3), Theorem 1 (i)) → sSup / sInf over all finite pure-state ensembles of every size, or over all unit vectors; reason: on the domain of the statement (channels, density matrices, nonempty spaces) every set is nonempty and bounded (0 ≤ · ≤ log₂ d_out) and the extremum is attained (Carathéodory, compact unit sphere), so the values coincide
--   - encoding: spaces C^{d×d}, H_in, H_{A1}, … of finite dimension → nonempty finite types (Fintype, DecidableEq, Nonempty) in Type; reason: a 0-dimensional space carries no state, so Nonempty excludes no instance of the paper
--   - encoding: quantum channel (CPT map) → QAlgorithms.IsChannel (a finite Kraus family with Σ A_k†A_k = I); reason: the paper gives this operator-sum form as an equivalent characterization of finite-dimensional CPT maps (pp.2–3)
--   - encoding: σ1 ⊗ σ2 with E_F "calculated over the bipartite A–B partition" → tensorState σ₁ σ₂ on (A₁ × A₂) × (B₁ × B₂), the Kronecker product regrouped to the cut A₁A₂ | B₁B₂; reason: this is the paper's cut; formation traces the second factor
--   - encoding: N1 ⊗ N2 → ShorEBAdditivity.tensorChannel N₁ N₂, defined on every operator by the matrix-unit expansion; reason: for linear maps it is the unique linear map with (N₁ ⊗ N₂)(X ⊗ Y) = N₁(X) ⊗ N₂(Y); it acts on entangled inputs too
-- source:
--   Shor, Equivalence of Additivity Questions in Quantum Information Theory, arXiv:quant-ph/0305035v4, §3, p. 7

import Mathlib
import Definitions.Def_ShorAdditivityEquiv_FormationAdditive
import Definitions.Def_ShorAdditivityEquiv_ConstrainedHolevoAdditive

namespace ShorAdditivityEquiv

/-- Shor, *Equivalence of Additivity Questions in Quantum Information Theory*, arXiv:quant-ph/0305035v4, §3, p.7, unnumbered: "Now, suppose EF(σ) is additive. I claim that χN(ρ) is as well, and
vice versa. [...] The first term on the right-hand side is additive, so the entanglement of
formation EF is additive if and only if the constrained capacity χN(ρ) is."

**Formalization Note.** Both sides are the global propositions: `FormationAdditive` (Theorem 1
(iii), all bipartite states of all finite dimensions) and `ConstrainedHolevoAdditive`
(`χ_{N1⊗N2}(ρ1 ⊗ ρ2) = χ_{N1}(ρ1) + χ_{N2}(ρ2)` for all channels and all input density matrices of
all finite dimensions). The argument passes between channels and states of different
dimensions (Stinespring dilations and `msw_converse`), so a statement for one fixed pair would
be a different claim. -/
theorem formationAdditive_iff_constrained :
    FormationAdditive ↔ ConstrainedHolevoAdditive := by sorry

end ShorAdditivityEquiv
