-- Prove2me | Theorems.Thm_RamseyLST_Main_corollary_10
-- name    : RamseyLST.Main.corollary_10
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T17:08:56.750395+00:00
-- url     : https://prove2.me/theorems/f50c2d4e-c503-4b4c-ab74-4a05c258008c
-- title:
--   Corollary 10 — a bounded-aspect-ratio subroutine yields (strong) Ramsey spanning trees with candidate core $A$
-- statement:
--   There is an absolute constant $c$, defining $\Phi_{\beta,t}=(\beta t)^{ct}$ (the aspect-ratio bound of Lemma 8), such that the following holds. Let $\mathcal X$ be a class of metric spaces, let $\alpha_0,C_D$ and $\psi$ be parameters, and let
--
--   $$t>1,\qquad \kappa\ge2,\qquad \beta\ge192\,C_D(\kappa+1),\qquad \zeta'=\frac{72\,C_D(\kappa+1)}{\beta},\qquad \alpha'=(1+\zeta')\alpha_0,\qquad \psi'=\Big(1-\frac1t\Big)\psi(2\Phi_{\beta,t}).$$
--
--   Let $G=(V,E,\ell)$ be a finite connected weighted graph with $(V,d_G)\in\mathcal X$, and let $A\subseteq V$ with $|A|\ge2$.
--
--   1. If Bounded-AR-ST-Embed satisfies Assumption 1 with parameters $\alpha_0,C_D,\psi$ on $\mathcal X(1+\zeta')$, then $G$ has an $(\alpha',\psi',2C_D)$-Ramsey spanning tree with candidate core $A$.
--   2. If it satisfies Assumption 1 strongly on $\mathcal X(1+\zeta')$, then $G$ has a strong $\big(\tfrac{\kappa+3}{\kappa-1}\alpha',\psi',2C_D\big)$-Ramsey spanning tree with candidate core $A$.
--
--   Taking $\mathcal X$ to be the class of all metric spaces gives the unrestricted form, since every finite metric space lies in $\mathcal X(1+\zeta')$. Corollary 10 is the reduction of the general problem to candidate cores of bounded aspect ratio, specialized to the candidate core of Lemma 8 with uniform weights.
--
--   Differences from the source:
--   - encoding: Bounded-AR-ST-Embed satisfies Assumption 1 (an algorithm) → every admissible input (G̃, Z̃^in, w̃) has an output with the Assumption-1 properties (the predicate Assumption1); reason: a deterministic subroutine is a function; ∀∃ is equivalent by choice
--   - generalization: Assumption 1 for every candidate core Z̃^in → Assumption 1 only for non-empty candidate cores; reason: a weaker hypothesis; the reduction only calls the subroutine on non-empty cores; avoids a vacuous hypothesis under 0^0 = 1
--   - encoding: Φ_{β,t} = (βt)^{O(t)}, the bound of Lemma 8 → ∃ an absolute c, chosen before every other quantity, with Φ_{β,t} = (βt)^{c·t}; reason: explicit constant for O(·); both this statement and Lemma 8 only become weaker as c grows (ψ is non-increasing), so a common c exists whenever each holds with its own
--   - generalization: a class 𝒳 of metric spaces → any predicate on (type, real distance), not required to be closed under isometry or to contain only metric spaces; reason: the argument uses only (V, d_G) ∈ 𝒳 and that the subroutine's inputs embed with distortion 1 + ζ into (V, d_G); every class of metric spaces is such a predicate
-- source:
--   Bartal, Hovav, Nearly Tight Low-Stretch Ramsey Spanning Trees, STOC 2027 submission (manuscript sha256 bcaed0afb9db0cccb453599c9f6915e958922563d3989766c4affc99a15de44d), pp. 21–22 (PDF 25–26), Corollary 10 (with the definition of Φ_{β,t} on p. 21)

import Mathlib
import Definitions.Def_ARTreeCover_WGraph
import Definitions.Def_RamseyLST_Main_FiniteMetric
import Definitions.Def_RamseyLST_Main_RamseySpanningTree
import Definitions.Def_RamseyLST_Main_Assumption1

open ARTreeCover

namespace RamseyLST.Main

/-- Corollary 10 (pp. 21–22): there is an absolute constant `c` (with `Φ_{β,t} = (βt)^{c t}`, the
aspect-ratio bound of Lemma 8) such that the following holds. Let `𝒳` be a class of metric spaces,
`α₀, C_D, ψ` parameters, `t > 1`, `κ ≥ 2`, `β ≥ 192 C_D (κ+1)`, `ζ' = 72 C_D (κ+1)/β`,
`α' = (1 + ζ') α₀` and `ψ' = (1 − 1/t) ψ(2Φ_{β,t})`. For every finite connected weighted graph `G`
with `(V, d_G) ∈ 𝒳` and every `A ⊆ V` with `|A| ≥ 2`: if the subroutine satisfies Assumption 1
on `𝒳(1 + ζ')`, then `G` has an `(α', ψ', 2C_D)`-Ramsey spanning tree with candidate core `A`; if
it satisfies Assumption 1 strongly on `𝒳(1 + ζ')`, then `G` has a strong
`((κ+3)/(κ−1) α', ψ', 2C_D)`-Ramsey spanning tree with candidate core `A`. -/
theorem corollary_10 :
    ∃ c : ℝ, ∀ (𝒳 : MetricClass) (α₀ CD : ℝ) (ψ : ℝ → ℝ) (t κ β : ℝ), 1 < t → 2 ≤ κ →
      192 * CD * (κ + 1) ≤ β →
      ∀ (V : Type) [Fintype V] [DecidableEq V] (G : WGraph V), G.graph.Connected →
        𝒳 V (rdist G) → ∀ A : Finset V, 2 ≤ A.card →
          (Assumption1 false (𝒳.within (1 + 72 * CD * (κ + 1) / β)) α₀ CD ψ →
            ∃ (T : SpanningTree G) (Z : Finset V),
              IsRamseySpanningTree false G T A Z ((1 + 72 * CD * (κ + 1) / β) * α₀)
                  ((1 - 1 / t) * ψ (2 * (β * t) ^ (c * t))) ∧
                DiamStretchLe G T (2 * CD)) ∧
          (Assumption1 true (𝒳.within (1 + 72 * CD * (κ + 1) / β)) α₀ CD ψ →
            ∃ (T : SpanningTree G) (Z : Finset V),
              IsRamseySpanningTree true G T A Z
                  ((κ + 3) / (κ - 1) * ((1 + 72 * CD * (κ + 1) / β) * α₀))
                  ((1 - 1 / t) * ψ (2 * (β * t) ^ (c * t))) ∧
                DiamStretchLe G T (2 * CD)) := by sorry

end RamseyLST.Main
