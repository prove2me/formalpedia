-- Prove2me | Theorems.Thm_SpatialDemandEq_Optimal_Supplement_lemma_4
-- name    : SpatialDemandEq.Optimal.Supplement.lemma_4
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-23T06:39:01.078302+00:00
-- url     : https://prove2.me/theorems/88f8b9cc-424f-4abe-84ce-4b73285910d4
-- title:
--   Lemma 4, p. 11 — I − D, with D_jk = λc/(μ_j − λA_j(w))² · ∂A_j/∂w_k, is an M-matrix
-- statement:
--   Work in the spatial service model (region $\mathcal S$, demand $\nu$, distances $d_k$, constants $c > 0$, $\lambda > 0$, under the standing assumptions), with arbitrary service rates $\mu \in \mathbb R^K$. Fix an arbitrary weight vector $w$ at which every area map $w \mapsto A_j(w)$ is differentiable, and define the $K \times K$ matrix
--   $$D_{jk} = \frac{\lambda c}{(\mu_j - \lambda A_j(w))^2}\cdot\frac{\partial A_j}{\partial w_k}.$$
--   Then $I - D$ is an M-matrix: its off-diagonal entries are nonpositive, and every (complex) eigenvalue of $I - D$ has positive real part.
--
--   This is the linear-algebra core of the comparative statics (Theorem 3): differentiating the equilibrium condition (3) gives linear systems $(I - D)w' = v$, and the monotonicity of M-matrices transfers the sign of $v$ to the derivative vector $w'$.
--
--   **Formalization Note** An M-matrix is defined as in the paper (p. 11): off-diagonal entries $\le 0$ and eigenvalues over $\mathbb C$ with positive real part. $\partial A_j/\partial w_k$ is the Fréchet derivative applied to the $k$-th unit vector.
--
--   Differences from the source:
--   - reading: the partial derivatives ∂A_j/∂w_k at w, presupposed to exist → the hypothesis that every area map w ↦ A_j(w) is (Fréchet) differentiable at w; reason: the paper writes the derivatives without stating a regularity condition; the proof uses Lemma 1 parts 3–4, which need it
--   - generalization: D_jk is undefined when μ_j = λA_j(w) → Lean's convention x/0 = 0 makes row j of D zero there; reason: this extends the definition to singular denominator rows without excluding any source-defined instance; the resulting coefficient is zero, so the row-sum and sign argument on p. 11 still applies
--   - generalization: positive service rates with total capacity greater than λ (§3.1, p. 7) → arbitrary real service rates μ, without positivity or aggregate-capacity assumptions; reason: the proof on p. 11 uses only nonnegativity of λc/(μ_j − λA_j(w))² and the derivative signs and row sums, so it applies to all these rates and specializes to every source instance
--   - encoding: the standing assumptions of §3.1 → the published `Standing` of the base mission; reason: inherited base conventions, disclosed on the published definition
-- source:
--   Carlsson, Peng & Ryzhov, Demand Equilibria in Spatial Service Systems, SSRN preprint 4794156 (version of 2024-04-14), p. 11, Lemma 4 (M-matrix defined on p. 11)

import Mathlib
import Definitions.Def_SpatialDemandEq_Optimal_Model
import Definitions.Def_SpatialDemandEq_Optimal_Supplement_MMatrix
import Definitions.Def_SpatialDemandEq_Optimal_Supplement_Model

open MeasureTheory SpatialDemandEq.Optimal

namespace SpatialDemandEq.Optimal.Supplement

theorem lemma_4 {n K : ℕ} (S : Set (E n)) (ν : Measure (E n)) (dst : E n → E n → ℝ)
    (xs : Fin K → E n) (c lam : ℝ) (hS : Standing S ν dst xs c lam) (μ : Fin K → ℝ)
    (w : Fin K → ℝ)
    (hdiff : ∀ j, DifferentiableAt ℝ
      (fun w' : Fin K → ℝ => area ν (cell S (distFn dst xs) w' j)) w) :
    IsMMatrix (1 - Dmat ν S (distFn dst xs) c lam μ w) := by sorry

end SpatialDemandEq.Optimal.Supplement
