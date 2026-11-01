-- Prove2me | Theorems.Thm_ShorAdditivityEquiv_theorem_1
-- name    : ShorAdditivityEquiv.theorem_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T15:31:59.407439+00:00
-- url     : https://prove2.me/theorems/ee3cdf5b-f645-403b-ad82-d00ad2c5bafc
-- title:
--   Theorem 1 — additivity of minimum output entropy, of Holevo capacity, of $E_F$, and strong superadditivity of $E_F$ are equivalent
-- statement:
--   The following four statements are equivalent.
--
--   1. **Additivity of the minimum output entropy.** For all quantum channels $N_1$, $N_2$ of all finite dimensions, $\min_{|\phi\rangle} H((N_1\otimes N_2)(|\phi\rangle\langle\phi|)) = \min_{|\phi\rangle} H(N_1(|\phi\rangle\langle\phi|)) + \min_{|\phi\rangle} H(N_2(|\phi\rangle\langle\phi|))$.
--   2. **Additivity of the Holevo capacity.** For all quantum channels $N_1$, $N_2$ of all finite dimensions, $\chi_{N_1\otimes N_2}=\chi_{N_1}+\chi_{N_2}$, with $\chi$ as in Eq. (1).
--   3. **Additivity of the entanglement of formation.** For all bipartite states $\sigma_1$ on $\mathcal H_{A_1}\otimes\mathcal H_{B_1}$ and $\sigma_2$ on $\mathcal H_{A_2}\otimes\mathcal H_{B_2}$, $E_F(\sigma_1\otimes\sigma_2)=E_F(\sigma_1)+E_F(\sigma_2)$, with $E_F$ as in Eq. (2) calculated over the $A$–$B$ partition.
--   4. **Strong superadditivity of the entanglement of formation.** For every density matrix $\sigma$ on $\mathcal H_{A_1}\otimes\mathcal H_{A_2}\otimes\mathcal H_{B_1}\otimes\mathcal H_{B_2}$, $E_F(\sigma)\ge E_F(\mathrm{Tr}_2\sigma)+E_F(\mathrm{Tr}_1\sigma)$, where $\mathrm{Tr}_1$ traces out $\mathcal H_{A_1}\otimes\mathcal H_{B_1}$ and $\mathrm{Tr}_2$ traces out $\mathcal H_{A_2}\otimes\mathcal H_{B_2}$.
--
--   Here $H$ is the von Neumann entropy and minima are over (unit) vectors of the input space. Each statement is a proposition about all channels or all states of all finite dimensions; the theorem asserts every implication between them. All four were open conjectures when the paper appeared; Hastings (2009) later showed (i), and hence all four, to be false. The equivalence is the theorem; the mission asserts neither the conjectures nor their negations.
--
--   Differences from the source:
--   - reading: "The following are equivalent" for statements (i)–(iv), each phrased for "two quantum channels" or "two quantum states" / "a density matrix σ" → List.TFAE of four global propositions, each quantifying over all finite dimensions and all channels / density matrices; reason: (i)–(iv) are conjectures about all channels / all states of all finite dimensions, and the proofs apply the hypothesis to auxiliary channels and states of other dimensions; a per-pair implication is a different (false) claim
--   - encoding: max / min over ensembles {p_i, |v_i⟩} or over vectors |φ⟩ (Eqs. (1)–(3), Theorem 1 (i)) → sSup / sInf over all finite pure-state ensembles of every size, or over all unit vectors; reason: on the domain of the statement (channels, density matrices, nonempty spaces) every set is nonempty and bounded (0 ≤ · ≤ log₂ d_out) and the extremum is attained (Carathéodory, compact unit sphere), so the values coincide
--   - encoding: spaces C^{d×d}, H_in, H_{A1}, … of finite dimension → nonempty finite types (Fintype, DecidableEq, Nonempty) in Type; reason: a 0-dimensional space carries no state, so Nonempty excludes no instance of the paper
--   - encoding: quantum channel (CPT map) → QAlgorithms.IsChannel (a finite Kraus family with Σ A_k†A_k = I); reason: the paper gives this operator-sum form as an equivalent characterization of finite-dimensional CPT maps (pp.2–3)
--   - encoding: vectors |φ⟩, |v_i⟩ of the input space → unit vectors (‖φ‖ = 1); reason: |φ⟩⟨φ| is meant as a state (p.4: "the minimization ranges over states |φ⟩"); ensemble members are states
--   - encoding: σ1 ⊗ σ2 with E_F "calculated over the bipartite A–B partition" → tensorState σ₁ σ₂ on (A₁ × A₂) × (B₁ × B₂), the Kronecker product regrouped to the cut A₁A₂ | B₁B₂; reason: this is the paper's cut; formation traces the second factor
--   - encoding: N1 ⊗ N2 → ShorEBAdditivity.tensorChannel N₁ N₂, defined on every operator by the matrix-unit expansion; reason: for linear maps it is the unique linear map with (N₁ ⊗ N₂)(X ⊗ Y) = N₁(X) ⊗ N₂(Y); it acts on entangled inputs too
-- source:
--   Shor, Equivalence of Additivity Questions in Quantum Information Theory, arXiv:quant-ph/0305035v4, Theorem 1, pp. 5–6

import Mathlib
import Definitions.Def_ShorAdditivityEquiv_MinOutputEntropyAdditive
import Definitions.Def_ShorAdditivityEquiv_HolevoCapacityAdditive
import Definitions.Def_ShorAdditivityEquiv_FormationAdditive
import Definitions.Def_ShorAdditivityEquiv_FormationStronglySuperadditive

namespace ShorAdditivityEquiv

/-- Shor, *Equivalence of Additivity Questions in Quantum Information Theory*, arXiv:quant-ph/0305035v4, Theorem 1, pp.5–6: "The following are equivalent.
i. The additivity of the minimum entropy output of a quantum channel. [...]
ii. The additivity of the Holevo capacity of a quantum channel, [...]
iii. Additivity of the entanglement of formation. [...]
iv. The strong superadditivity of the entanglement of formation. [...]"

Each of (i)–(iv) is a global proposition, asserted for all channels or all states of all finite
dimensions: `MinOutputEntropyAdditive`, `HolevoCapacityAdditive`, `FormationAdditive`,
`FormationStronglySuperadditive`. The theorem asserts that the four are equivalent (every
implication between them).

**Formalization Note.** Conventions are those of the four definitions: nonempty finite index
types in `Type`; `QAlgorithms.IsChannel` for "CPT map"; `QAlgorithms.vnEntropy` (bits) for `H`;
maxima and minima as `sSup`/`sInf` (attained on this domain); pure-state ensembles in Eq. (1);
`E_F` the published P08 `formation` (Eq. (2)); `σ₁ ⊗ σ₂` regrouped to the cut `A₁A₂ | B₁B₂`.
The four conjectures themselves were later shown false (Hastings 2009); their equivalence is the
theorem stated here, and neither the conjectures nor their negations are asserted. -/
theorem theorem_1 :
    List.TFAE [MinOutputEntropyAdditive, HolevoCapacityAdditive, FormationAdditive,
      FormationStronglySuperadditive] := by sorry

end ShorAdditivityEquiv
