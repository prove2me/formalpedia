-- Prove2me | Theorems.Thm_TeschlODE_Horseshoe_horseshoe_topEquiv_shiftZ
-- name    : TeschlODE.Horseshoe.horseshoe_topEquiv_shiftZ
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-29T06:23:26.188378+00:00
-- url     : https://prove2.me/theorems/4f200058-b3bb-4eab-bed0-22c1568c49e6
-- title:
--   Theorem 13.1 — the Smale horseshoe has an invariant Cantor set on which it is conjugate to the two-sided shift, hence chaotic
-- statement:
--   Let $0 < \lambda < \tfrac12$ and $\mu > 2$, and let $F : \mathbb{R}^2 \to \mathbb{R}^2$ be a Smale horseshoe map: $F(x,y) = (\lambda x, \mu y)$ on $J_0 = [0,1] \times [0, 1/\mu]$ and $F(x,y) = (1 - \lambda x, \mu(1-y))$ on $J_1 = [0,1] \times [1 - 1/\mu, 1]$. Let
--   $$\Lambda = \Lambda(T_{1/\lambda}) \times \Lambda(T_\mu)$$
--   (13.8), and let $\varphi : \Lambda \to \Sigma_2 = \{0,1\}^{\mathbb{Z}}$ be the two-sided itinerary map (13.9). The book states: *The Smale horseshoe map has an invariant Cantor set $\Lambda$ on which the dynamics is equivalent to the double sided shift on two symbols. In particular it is chaotic.* Formally:
--
--   1. $\Lambda$ is a Cantor set (compact, totally disconnected, perfect);
--   2. $F(\Lambda) = \Lambda$;
--   3. $\varphi$ is a bijection of $\Lambda$ onto $\Sigma_2$ and $\sigma \circ \varphi = \varphi \circ F$ on $\Lambda$, where $\sigma(s)_n = s_{n+1}$ is the two-sided shift;
--   4. $\varphi$ and $\varphi^{-1}$ are continuous, with $\Lambda \subseteq \mathbb{R}^2$ and $\Sigma_2$ carrying the metric (11.35);
--   5. the restricted system $(\Lambda, F|_\Lambda)$ is chaotic: $F|_\Lambda$ is continuous, $\Lambda$ is infinite, $F|_\Lambda$ is topologically transitive and its periodic points are dense in $\Lambda$.
--
--   The horseshoe is the model of the dynamics near a transverse homoclinic point (Smale–Birkhoff, Theorem 13.2), and so the source of chaos in the Melnikov criterion of §13.3.
--
--   **Formalization Note.** *Parameters (correction to the page).* The book fixes $\lambda \in (0, \tfrac12]$ and $\mu \in [2, \infty)$. At $\mu = 2$ the strips $J_0, J_1$ meet on $y = \tfrac12$, where (13.2) and (13.3) disagree, and $\Lambda(T_2) = [0,1]$ is not a Cantor set. At $\lambda = \tfrac12$ the images $K_0, K_1$ meet and $\Lambda(T_2) = [0,1]$ again. The theorem is therefore stated for $\lambda \in (0, \tfrac12)$ and $\mu > 2$.
--
--   *Extension.* $F$ is any map agreeing with (13.2)–(13.3) on $J_0 \cup J_1$, and the conclusion holds for every such extension, since $\Lambda \subseteq J_0 \cup J_1$.
--
--   *Topology.* $\mathbb{R}^2$ is `ℝ × ℝ` with Mathlib's max-distance, which has the same topology as the Euclidean one. "Equivalent" is topological equivalence (11.10), spelled out as clauses 2–4, with continuity in $\varepsilon$–$\delta$ form. "Chaotic" is the book's definition of p. 296 (no sensitive-dependence axiom), applied to the subtype $\Lambda$.
-- source:
--   Teschl, Ordinary Differential Equations and Dynamical Systems (author's preliminary version of AMS GSM 140, 2012), p. 333, Theorem 13.1

import Mathlib
import Definitions.Def_TeschlODE_Horseshoe_IsHorseshoeMap
import Definitions.Def_TeschlODE_Horseshoe_horseshoeSet
import Definitions.Def_TeschlODE_Horseshoe_horseshoeItinerary
import Definitions.Def_TeschlODE_Horseshoe_shiftZ
import Definitions.Def_TeschlODE_Horseshoe_symDistZ
import Definitions.Def_TeschlODE_Horseshoe_IsCantorSet
import Definitions.Def_TeschlODE_Shared_IsChaotic

namespace TeschlODE.Horseshoe

/-- Teschl, Theorem 13.1, p. 333: the Smale horseshoe map has an invariant Cantor set `Λ` on which
the dynamics is equivalent to the double sided shift on two symbols; in particular it is
chaotic.

Here `F` is any map agreeing with (13.2) on `J₀` and with (13.3) on `J₁` (its values elsewhere
are arbitrary, as in the book), `Λ = Λ(T_{1/λ}) × Λ(T_µ)` is the set (13.8), and `ϕ` is the
itinerary map (13.9). The conclusion: `Λ` is a Cantor set; `F(Λ) = Λ`; `ϕ` is a bijection from
`Λ` onto `Σ₂ = {0, 1}^ℤ`; `σ ∘ ϕ = ϕ ∘ F` on `Λ` (σ the two-sided shift); `ϕ` and `ϕ⁻¹` are
continuous (ε–δ, `Λ ⊆ ℝ²` with its usual topology and `Σ₂` with the metric (11.35)); and the
restricted system `(Λ, F|_Λ)` is chaotic in the sense of p. 296.

Correction to the page: the book fixes `λ ∈ (0, 1/2]`, `µ ∈ [2, ∞)`. At `µ = 2` the strips `J₀`,
`J₁` meet on `y = 1/2`, where (13.2) and (13.3) disagree, and `Λ(T₂) = [0, 1]` is not a Cantor
set; at `λ = 1/2` the images `K₀`, `K₁` meet and `Λ(T₂) = [0, 1]` again. The theorem is stated for
`λ ∈ (0, 1/2)` and `µ > 2`. -/
theorem horseshoe_topEquiv_shiftZ (lam μ : ℝ) (hlam₀ : 0 < lam) (hlam : lam < 1 / 2)
    (hμ : 2 < μ) (F : ℝ × ℝ → ℝ × ℝ) (hF : IsHorseshoeMap lam μ F) :
    IsCantorSet (horseshoeSet lam μ) ∧
      F '' horseshoeSet lam μ = horseshoeSet lam μ ∧
      Set.BijOn (horseshoeItinerary lam μ F) (horseshoeSet lam μ) Set.univ ∧
      (∀ p ∈ horseshoeSet lam μ,
        shiftZ (horseshoeItinerary lam μ F p) = horseshoeItinerary lam μ F (F p)) ∧
      (∀ p ∈ horseshoeSet lam μ, ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
        ∀ q ∈ horseshoeSet lam μ, dist q p < δ →
          symDistZ 2 (horseshoeItinerary lam μ F q) (horseshoeItinerary lam μ F p) < ε) ∧
      (∀ p ∈ horseshoeSet lam μ, ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
        ∀ q ∈ horseshoeSet lam μ,
          symDistZ 2 (horseshoeItinerary lam μ F q) (horseshoeItinerary lam μ F p) < δ →
            dist q p < ε) ∧
      ∃ h : Set.MapsTo F (horseshoeSet lam μ) (horseshoeSet lam μ),
        TeschlODE.Shared.IsChaotic (h.restrict F (horseshoeSet lam μ) (horseshoeSet lam μ)) := by sorry

end TeschlODE.Horseshoe
