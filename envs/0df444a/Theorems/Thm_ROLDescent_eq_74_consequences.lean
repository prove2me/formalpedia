-- Prove2me | Theorems.Thm_ROLDescent_eq_74_consequences
-- name    : ROLDescent.eq_74_consequences
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T21:45:10.166087+00:00
-- url     : https://prove2.me/theorems/1a69aa04-0920-4d50-8d77-44937f995f41
-- title:
--   Consequences of (73)–(74) — orthogonal splitting $\mathcal I_\tau=\mathcal I_{\tau i}\oplus\mathcal U_{\tau,i}$ and $\bigcap_i\mathcal U_{\tau,i}=\{0\}$
-- statement:
--   Let $(\mathcal I_\tau)$ be a subspace hierarchy (73) in a finite-dimensional complex Hilbert space $\mathcal K$, let $\tau$ be an internal face, and put $\mathcal U_{\tau,i} = \mathcal I_\tau \cap \mathcal I_{\tau i}^\perp$ for $i \in N_\tau$. Then for every $i \in N_\tau$:
--
--   1. $\mathcal I_\tau = \mathcal I_{\tau i} + \mathcal U_{\tau,i}$ and $\mathcal I_{\tau i} \perp \mathcal U_{\tau,i}$, i.e. $\mathcal I_\tau = \mathcal I_{\tau i} \oplus \mathcal U_{\tau,i}$ orthogonally;
--   2. $E_{\tau,i} = \Pi_\tau - \Pi_{\tau i}$ is the orthogonal projection onto the removed subspace $\mathcal U_{\tau,i}$;
--
--   and moreover the removed subspaces have trivial intersection:
--
--   $$\bigcap_{i \in N_\tau} \mathcal U_{\tau,i} = \{0\}.$$
--
--   The last identity follows from the span condition and is the qualitative reason the Gram norm is below one.
--
--   **Formalization Note** The intersection is taken inside $\mathcal I_\tau$ (the $\mathcal U_{\tau,i}$ are subspaces of $\mathcal I_\tau$).
--
--   Differences from the source:
--   - generalization: in the hierarchy of Section 5.1 (weighted pure complex) → only the structural requirements (73) on the subspaces; no weights, purity or connectivity assumed; reason: the consequences use only (73); the Section 5.1 hierarchy satisfies it
--   - encoding: I_τ = I_τi ⊕ U_τ,i → I_τi ⊔ U_τ,i = I_τ and I_τi ⟂ U_τ,i; reason: definition of an orthogonal direct sum of subspaces
--   - encoding: ⋂_{i∈N_τ} U_τ,i = {0} (intersection of subspaces of I_τ) → I_τ ⊓ ⨅_{i∈N_τ} U_τ,i = ⊥ in the submodule lattice of K; reason: the U_τ,i lie in I_τ, so this is the same intersection, and it stays correct if the index set were empty
-- source:
--   Hayakawa, Recursive Operator Localization and Spectral Gap Descent via the Geometry of Local Spectral Expansion, arXiv:2610.23695 (held version, sha256 702bd512…20bdd545), Section 5.1.2, after eq. (74), p.31 (PDF 31)

import Mathlib
import Definitions.Def_HDXConc_linkWeight
import Definitions.Def_ROLDescent_IsSubspaceHierarchy

namespace ROLDescent

/-- **Consequences of (73)–(74): orthogonal splitting into child and removed spaces.**
Hayakawa, *Recursive Operator Localization and Spectral Gap Descent via the Geometry of Local
Spectral Expansion*, arXiv:2610.23695 (held version, sha256 702bd512…20bdd545), Section 5.1.2, after eq. (74), p.31 (PDF 31): "In particular, U_τ,i := I_τ ∩ I_τi^⊥,
I_τ = I_τi ⊕ U_τ,i, ⋂_{i∈N_τ} U_τ,i = {0}. Thus E_τ,i is the orthogonal projection onto the
removed subspace U_τ,i. The last identity follows from the span condition."

**Formalization Note** Only the structural requirements (73) are assumed (no weights). The orthogonal
direct sum is stated as "`I_τi ⊔ U_τ,i = I_τ` and `I_τi ⟂ U_τ,i`"; `E_τ,i = Π_τ − Π_τi` is a
difference of `starProjection`s. The intersection of the removed spaces is taken inside `I_τ`
(`I τ ⊓ ⨅ …`), as the `U_τ,i` are subspaces of `I_τ`. -/
theorem eq_74_consequences {V : Type*} [Fintype V] [DecidableEq V]
    {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [FiniteDimensional ℂ K]
    (X : Finset (Finset V)) (d : ℕ) (I : Finset V → Submodule ℂ K)
    (hI : IsSubspaceHierarchy X d I) (τ : Finset V) (hτ : τ ∈ X) (hτd : τ.card + 2 ≤ d) :
    (∀ i ∈ HDXConc.linkVerts X τ,
      I (insert i τ) ⊔ (I τ ⊓ (I (insert i τ))ᗮ) = I τ ∧
      I (insert i τ) ⟂ (I τ ⊓ (I (insert i τ))ᗮ) ∧
      (I τ).starProjection - (I (insert i τ)).starProjection =
        (I τ ⊓ (I (insert i τ))ᗮ).starProjection) ∧
    I τ ⊓ (⨅ i ∈ HDXConc.linkVerts X τ, I τ ⊓ (I (insert i τ))ᗮ) = ⊥ := by sorry

end ROLDescent
