-- Prove2me | Theorems.Thm_ScholtesStab_step1_codimensions
-- name    : ScholtesStab.step1_codimensions
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:23:36.983903+00:00
-- url     : https://prove2.me/theorems/92e6f83c-10b7-465b-8e6e-a33c7e9a6c9a
-- title:
--   Proof of Theorem 1, Step 1: codimensions of $\mathcal T_{\bar x}$ and $\mathcal T^{\mathcal S}_{x}$
-- statement:
--   1. If $\bar x\in M$ satisfies MPCC-LICQ, then
--
--   $$
--   \dim\mathcal T_{\bar x}+|a_{01}(\bar x)|+|a_{10}(\bar x)|+2\,|a_{00}(\bar x)|=n .
--   $$
--
--   2. If $t>0$ and $x\in M^{\mathcal S}$ satisfies LICQ, then
--
--   $$
--   \dim\mathcal T^{\mathcal S}_x+|\mathcal H(x)|+|\mathcal N_1(x)|+|\mathcal N_2(x)|=n .
--   $$
--
--   So the codimensions are $\alpha=|a_{01}(\bar x)|+|a_{10}(\bar x)|+2|a_{00}(\bar x)|$ and $\alpha^{\mathcal S}_t=|\mathcal H(x)|+|\mathcal N_1(x)|+|\mathcal N_2(x)|$, the counting step behind the index comparison in the proof of Theorem 1.
--
--   Differences from the source:
--   - encoding: ℝⁿ, indices j = 1, …, κ → EuclideanSpace ℝ (Fin n), indices in Fin κ (0-based); reason: a relabelling of coordinates and indices; same instances
--   - encoding: f, F₁, F₂ twice continuously differentiable (standing assumption, p.1) → ContDiff ℝ 2 fields of the structure MPCC; reason: the standing assumption is carried by every instance; same instances
--   - encoding: differentials DF(x), Hessians D²L(x) → fderiv ℝ F x : ℝⁿ →L[ℝ] ℝ and fderiv ℝ (fderiv ℝ L) x as a bilinear form; reason: the Fréchet derivative of a C² function is its differential and its second derivative is the Hessian; linear independence of differentials is that of gradients
--   - generalization: α = |a₀₁(x̄)| + 2|a₀₀(x̄)| under the proof's assumption a₁₀(x̄) = ∅ (p.18, "without loss of generality") → the general statement with the a₁₀ terms; reason: setting a₁₀(x̄) = ∅ makes the a₁₀ terms vanish and gives the printed claim
--   - encoding: codimension α of 𝒯_x̄, αˢ_t of 𝒯ˢ_xᵗ → dim + count = n, with dim = Module.finrank; reason: the codimension of a subspace of ℝⁿ is n minus its dimension; the additive form avoids truncated subtraction
-- source:
--   Lämmel & Shikhman, On stability of the Scholtes regularization for mathematical programs with complementarity constraints, arXiv:2501.07383v2, Proof of Theorem 1, Step 1, p.18

import Mathlib
import Definitions.Def_ScholtesStab_MPCC
import Definitions.Def_ScholtesStab_MPCC_a01
import Definitions.Def_ScholtesStab_MPCC_MPCCLICQ
import Definitions.Def_ScholtesStab_MPCC_lagrangian
import Definitions.Def_ScholtesStab_MPCC_H
import Definitions.Def_ScholtesStab_MPCC_LICQ
import Definitions.Def_ScholtesStab_MPCC_lagrangianS

namespace ScholtesStab

open MPCC

/-- **The codimensions of `𝒯_x̄` and `𝒯ˢ_x`.** Lämmel–Shikhman, arXiv:2501.07383v2, Proof of
Theorem 1, Step 1, p.18: "We denote the codimensions of 𝒯_x̄ and 𝒯ˢ_xᵗ, respectively, as
α = |a₀₁(x̄)| + 2|a₀₀(x̄)|, αˢ_t = |ℋ(xᵗ)| + |𝒩₁(xᵗ)| + |𝒩₂(xᵗ)|."

(i) If `x̄ ∈ M` satisfies MPCC-LICQ, then `dim 𝒯_x̄ + |a₀₁(x̄)| + |a₁₀(x̄)| + 2|a₀₀(x̄)| = n`.
(ii) If `t > 0` and `x ∈ Mˢ` satisfies LICQ, then `dim 𝒯ˢ_x + |ℋ(x)| + |𝒩₁(x)| + |𝒩₂(x)| = n`.

**Formalization Note.** The proof assumes `a₁₀(x̄) = ∅` without loss of generality, so its α
omits `|a₁₀(x̄)|`; (i) is the general count. Dimensions are `Module.finrank`, and the
codimension identities are stated additively (no natural-number subtraction). -/
theorem step1_codimensions {n κ : ℕ} (P : MPCC n κ) (xbar : E n) (t : ℝ) (x : E n)
    (hxbar : xbar ∈ P.M) (hLICQbar : P.MPCCLICQ xbar)
    (ht : 0 < t) (hx : x ∈ P.MS t) (hLICQ : P.LICQ t x) :
    Module.finrank ℝ (P.tangentSpace xbar)
        + ((P.a01 xbar).card + (P.a10 xbar).card + 2 * (P.a00 xbar).card) = n ∧
      Module.finrank ℝ (P.tangentSpaceS t x)
        + ((P.H t x).card + (P.N1 x).card + (P.N2 x).card) = n := by sorry

end ScholtesStab
