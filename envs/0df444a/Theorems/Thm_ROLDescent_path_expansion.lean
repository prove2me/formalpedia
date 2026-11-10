-- Prove2me | Theorems.Thm_ROLDescent_path_expansion
-- name    : ROLDescent.path_expansion
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T21:49:49.950407+00:00
-- url     : https://prove2.me/theorems/0d6a3987-7e87-40bc-b8a9-40a426cb8e95
-- title:
--   Proof of Theorem 5.2 — path expansion $\delta_\emptyset=\min_p\delta_{\tau_j}\prod_{k<j}(1-\bar\theta_{\tau_k})$
-- statement:
--   Let $(X, w)$ be a weighted pure complex with facet size $d \ge 2$. Let $\bar\theta$ and $\delta$ be real functions on faces with $\bar\theta_\tau < 1$ at every internal face and
--
--   $$\delta_\tau = (1 - \bar\theta_\tau) \min_{i \in N_\tau} \delta_{\tau i} \qquad (\tau \in \mathcal T_{\mathrm{int}}).$$
--
--   Then for every $0 \le j \le d - 1$,
--
--   $$\delta_\emptyset = \min_{\emptyset = \tau_0 \to \tau_1 \to \dots \to \tau_j} \Big\{ \delta_{\tau_j} \prod_{k=0}^{j-1} (1 - \bar\theta_{\tau_k}) \Big\},$$
--
--   the minimum being over root paths of $j$ steps (ordered sequences of legal additions), with the empty product equal to one. At $j = d - 1$ this is the path formula (84) for $\delta_\emptyset$.
--
--   Differences from the source:
--   - generalization: inside the proof of Theorem 5.2, under its hypotheses → only θ̄_τ < 1 at internal faces and (83), on a weighted pure complex; reason: the hypotheses of Theorem 5.2 give θ̄_τ < 1 (its first conclusion), so this specializes to the source's setting
--   - encoding: paths τ₀ = ∅ → τ₁ → ⋯ → τ_j; min over paths → rootPaths X j (injective vertex sequences with face prefixes), τ_k = prefixFace p k; ⨅ over this finite nonempty set; reason: a step τ → τi is determined by its added vertex; different orders remain different paths
-- source:
--   Hayakawa, Recursive Operator Localization and Spectral Gap Descent via the Geometry of Local Spectral Expansion, arXiv:2610.23695 (held version, sha256 702bd512…20bdd545), proof of Theorem 5.2, p.35 (PDF 35)

import Mathlib
import Definitions.Def_ROLDescent_WeightedComplex
import Definitions.Def_HDXConc_linkWeight
import Definitions.Def_ROLDescent_prefixFace
import Definitions.Def_ROLDescent_rootPaths

namespace ROLDescent

/-- **Path expansion of δ_∅.** Hayakawa, *Recursive Operator Localization and Spectral Gap Descent via the Geometry of Local
Spectral Expansion*, arXiv:2610.23695 (held version, sha256 702bd512…20bdd545), proof of Theorem 5.2, p.35 (PDF 35): "To make the path
formula explicit, write a root-to-stop path as p = (τ₀, …, τ_{d−1}), where τ₀ = ∅ and
τ_{d−1} = t(p). At each internal node, (83) reads δ_τ = min_{i∈N_τ} (1 − θ̄_τ)δ_τi. The retention
factor is positive, so substituting the same formula for each child lets us combine the
successive minima. More generally, after j steps, for 0 ≤ j ≤ d − 1,
δ_∅ = min_{τ₀=∅→τ₁→⋯→τ_j} { δ_τj ∏_{k=0}^{j−1} (1 − θ̄_τk) }, with the empty product equal to one."

**Formalization Note** A path of `j` steps is an element of `rootPaths X j` (an injective sequence of
added vertices with face prefixes); τ_k is `prefixFace p k`. The hypotheses are the weighted complex,
the positivity of the retention factors (θ̄_τ < 1 on T_int, `τ.card + 2 ≤ d`) and the recursion (83)
as an equation. The minimum over paths is an infimum over the finite, nonempty set of paths. -/
theorem path_expansion {V : Type*} [Fintype V] [DecidableEq V]
    (X : Finset (Finset V)) (d : ℕ) (w : Finset V → ℝ) (hX : WeightedComplex X d w)
    (θbar δ : Finset V → ℝ)
    (hθ : ∀ τ ∈ X, τ.card + 2 ≤ d → θbar τ < 1)
    (h83 : ∀ τ ∈ X, τ.card + 2 ≤ d →
      δ τ = (1 - θbar τ) * ⨅ i : HDXConc.linkVerts X τ, δ (insert (i : V) τ)) :
    ∀ j ≤ d - 1, δ ∅ = ⨅ p : rootPaths X j,
      δ (prefixFace p.1 j) * ∏ k ∈ Finset.range j, (1 - θbar (prefixFace p.1 k)) := by sorry

end ROLDescent
