-- Prove2me | Theorems.Thm_ROLDescent_proposition_5_3
-- name    : ROLDescent.proposition_5_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T21:47:26.2542+00:00
-- url     : https://prove2.me/theorems/3137035b-cf71-4e01-baa5-8b4eb6aafd2a
-- title:
--   Proposition 5.3 — Gram descent $\theta_\tau\le\bar\theta_\tau<1$ on $\mathcal T_{\mathrm{int}}$
-- statement:
--   Let $(X, w)$ be a weighted pure complex with facet size $d \ge 2$ whose link graphs with $m_\tau \ge 2$ are connected (the 1-skeleton of the link of every face with $|\tau| + 2 \le d$ is a connected graph), and let $(\mathcal I_\tau)$ be a subspace hierarchy (73) in a finite-dimensional complex Hilbert space $\mathcal K$. Write $\mathcal T_{\mathrm{int}}$ for the internal faces ($|\tau| \le d - 2$), $\mathcal T_{\mathrm{bot}}$ for those with $|\tau| = d - 2$, and $\mathcal T_{\mathrm{stop}}$ for the faces with $|\tau| = d - 1$. Take
--
--   1. bottom Gram bounds $\bar\theta_{\tau_\star}$ on $\mathcal T_{\mathrm{bot}}$ with $\theta_{\tau_\star} \le \bar\theta_{\tau_\star} < 1$ and $\bar\theta_{\tau_\star} \ge 0$ (78);
--   2. link-walk gap bounds $\lambda_\tau \in (0, 2]$ with $\mathrm{gap}(\mathrm{id} - P_\tau) \ge \lambda_\tau$ on $\mathcal T_{\mathrm{int}} \setminus \mathcal T_{\mathrm{bot}}$ (72);
--   3. the remaining Gram bounds defined by $\bar\theta_\tau = F_{\lambda_\tau}(c^\downarrow_\tau)$ with $c^\downarrow_\tau = \max_{i \in N_\tau} \bar\theta_{\tau i}$ (79), subject to $c^\downarrow_\tau < \lambda_\tau / 2$ (80), on $\mathcal T_{\mathrm{int}} \setminus \mathcal T_{\mathrm{bot}}$.
--
--   Then for every internal face $\tau$,
--
--   $$\theta_\tau \le \bar\theta_\tau < 1 .$$
--
--   The proposition is the geometric half of the spectral-descent theorem: it propagates the bottom Gram bounds and the link-walk gaps to explicit Gram bounds at every level.
--
--   Differences from the source:
--   - encoding: θ̄_τ defined recursively by (79) above T_bot → an input function θbar satisfying (79) as an equation on faces with τ.card + 3 ≤ d; reason: the recursion on d − |τ| determines θ̄ uniquely from the bottom bounds; same instances
--   - encoding: gap(id − P_τ) ≥ λ_τ in L²(π_τ) (72) → LinkGapGE: HDXConc.SecondEigLE on N_τ (HDXConc.linkVerts) with the zero-diagonal weights W_τij (HDXConc.linkWeight) and threshold 1 − λ_τ; reason: P_τ is the walk of these weights and is self-adjoint in L²(π_τ); Courant–Fischer
--   - encoding: max_{i∈N_τ} θ̄_τi; the levels T_int, T_bot, T_stop → ⨆ over the finite nonempty subtype N_τ; τ.card + 2 ≤ d, τ.card + 2 = d, τ.card + 1 = d; reason: N_τ is nonempty at internal faces, so the supremum is the maximum
--   - encoding: Gram norm θ_τ = ‖Σ π_τ(i) E_τ,i|_{I_τ}‖ → norm of the map I_τ → K obtained by composing with the inclusion; reason: the range lies in I_τ and the inclusion is isometric
--   - encoding: each link graph with m_τ ≥ 2 is connected (p.30) → SteurerHDX.IsConnectedComplex X d: the 1-skeleton of SteurerHDX.link X τ, whose vertices are the singletons {x} with x ∈ N_τ and whose edges are the pairs with τ ∪ {x, y} ∈ X, is connected for every face with τ.card + 2 ≤ d; reason: this graph is isomorphic to the link graph on N_τ (x ↦ {x}); same instances
-- source:
--   Hayakawa, Recursive Operator Localization and Spectral Gap Descent via the Geometry of Local Spectral Expansion, arXiv:2610.23695 (held version, sha256 702bd512…20bdd545), Proposition 5.3, p.35 (PDF 35)

import Mathlib
import Definitions.Def_ROLDescent_WeightedComplex
import Definitions.Def_HDXConc_linkWeight
import Definitions.Def_ROLDescent_outProb
import Definitions.Def_SteurerHDX_IsConnectedComplex
import Definitions.Def_ROLDescent_LinkGapGE
import Definitions.Def_ROLDescent_IsSubspaceHierarchy
import Definitions.Def_ROLDescent_gramNorm
import Definitions.Def_ROLDescent_gramUpdate

namespace ROLDescent

/-- **Proposition 5.3 (Gram descent through the hierarchy).** Hayakawa, *Recursive Operator Localization and Spectral Gap Descent via the Geometry of Local
Spectral Expansion*, arXiv:2610.23695 (held version, sha256 702bd512…20bdd545), Proposition 5.3, p.35
(PDF 35): "Consider the subspace hierarchy of Section 5.1, with classical link-walk gap bounds
(72) and bottom Gram bounds (78). Define the remaining Gram bounds by (79) and assume (80). Then
θ_τ ≤ θ̄_τ < 1 (τ ∈ T_int)."

**Formalization Note** The hierarchy of Section 5.1: a weighted pure complex with connected link
graphs (p.30; public `SteurerHDX.IsConnectedComplex`: the 1-skeleton of the link of every face
with `τ.card + 2 ≤ d` is connected) and a subspace hierarchy (73). Internal faces T_int are the faces with `τ.card + 2 ≤ d`; the bottom level T_bot (68) is
`τ.card + 2 = d`; T_int \ T_bot (m_τ ≥ 3) is `τ.card + 3 ≤ d`; stopping faces T_stop (67) are
`τ.card + 1 = d`. The Gram bounds θ̄ (overlined on the page) are an input function `θbar`, free on
T_bot (78) and satisfying the recursion (79) as an equation above it; this determines θ̄ uniquely
from the bottom inputs. `gramNorm` is the Gram norm θ_τ (75). The link-walk gap bounds λ_τ ∈ (0, 2]
(p.30) satisfy (72) on T_int \ T_bot. The maximum over the children is a supremum over the
(nonempty, finite) link vertices. -/
theorem proposition_5_3 {V : Type*} [Fintype V] [DecidableEq V]
    {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [FiniteDimensional ℂ K]
    (X : Finset (Finset V)) (d : ℕ) (w : Finset V → ℝ)
    (hX : WeightedComplex X d w) (hconn : SteurerHDX.IsConnectedComplex X d)
    (I : Finset V → Submodule ℂ K) (hI : IsSubspaceHierarchy X d I)
    (θbar lam : Finset V → ℝ)
    (h78 : ∀ τ ∈ X, τ.card + 2 = d →
      gramNorm X d w I τ ≤ θbar τ ∧ θbar τ < 1 ∧ 0 ≤ θbar τ)
    (h72 : ∀ τ ∈ X, τ.card + 3 ≤ d →
      0 < lam τ ∧ lam τ ≤ 2 ∧ LinkGapGE X d w τ (lam τ))
    (h79 : ∀ τ ∈ X, τ.card + 3 ≤ d →
      θbar τ = gramUpdate (lam τ) (⨆ i : HDXConc.linkVerts X τ, θbar (insert (i : V) τ)))
    (h80 : ∀ τ ∈ X, τ.card + 3 ≤ d →
      (⨆ i : HDXConc.linkVerts X τ, θbar (insert (i : V) τ)) < lam τ / 2) :
    ∀ τ ∈ X, τ.card + 2 ≤ d → gramNorm X d w I τ ≤ θbar τ ∧ θbar τ < 1 := by sorry

end ROLDescent
